module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Kunneth

/-!
# The Hodge Künneth map for schemes over a field, and the reduction to the fibre product

Let `k` be a field, `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` schemes over `k`, and `p : P ⟶ X`,
`q : P ⟶ Y` morphisms with `p ≫ f = q ≫ g`, so that `P` is a scheme over `k` through `p ≫ f`.
In every bidegree `(r, s)` the external cup product gives the `k`-linear Künneth map

`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(P, Ω^r_{P/k})`,
`ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`.

It is natural in `P`: precomposing `p` and `q` with a morphism `e : P' ⟶ P` composes the Künneth
map with `e^*`, since pullback is functorial and multiplicative. When `e` is an isomorphism, `e^*`
is bijective, so whether the Künneth map is bijective depends on `P` only up to isomorphism over
`X` and `Y`. Every fibre product of `X` and `Y` over `Spec k` is isomorphic over `X` and `Y` to the
chosen pullback `X ×_k Y`, so axiom (A5) for Hodge cohomology (Section 0FID, Remark 0FWE) follows
from the Künneth formula for `X ×_k Y` with its two projections, in every bidegree.

## Main definitions

* `Stacks.HodgeWeil.hodgeComponentPullbackOverField`: the pullback
  `H^q(X, Ω^p_{X/k}) ⟶ H^q(X', Ω^p_{X'/k})` along a morphism of `k`-schemes, `k`-linearly.
* `Stacks.HodgeWeil.hodgeComponentPullbackOverFieldEquiv`: the same along an isomorphism, as a
  `k`-linear equivalence.
* `Stacks.HodgeWeil.hodgeSchemeExternalCup`: the external cup product `(ξ, ζ) ↦ p^*ξ ∪ q^*ζ`.
* `Stacks.HodgeWeil.hodgeKunnethBidegreeMapOfSquares`: the Künneth map in bidegree `(r, s)` for
  a `k`-scheme `fP : P ⟶ Spec k` with morphisms `p`, `q` over `Spec k` to `X` and `Y`.
* `Stacks.HodgeWeil.hodgeSchemeKunnethMap`: the Künneth map in bidegree `(r, s)` for `P` a
  `k`-scheme through `p ≫ f`.

## Main results

* `Stacks.HodgeWeil.hodgeSchemeKunnethMap_lof_tmul`: on `ξ ⊗ ζ` the Künneth map is
  `p^*ξ ∪ q^*ζ`.
* `Stacks.HodgeWeil.hodgeKunnethBidegreeMapOfSquares_comp`: naturality in `P`.
* `Stacks.HodgeWeil.bijective_hodgeSchemeKunnethMap_iso_iff`: bijectivity of the Künneth map is
  invariant under isomorphism of `P`.
* `Stacks.HodgeWeil.bijective_hodgeKunnethBidegreeMap_of_pullback`: **the Künneth map of every
  fibre product of `X` and `Y` is bijective in a bidegree as soon as that of the chosen pullback
  `X ×_k Y` is.**

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open scoped TensorProduct
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent reindexHodgeDeg hodgeCohomologyCup
  hodgeCupProduct_add_left hodgeCupProduct_add_right reindexHodgeDeg_add)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k]

/-! ### Pullback along a morphism of `k`-schemes -/

section Pullback

variable {X X' X'' : Scheme.{u}} (g' : X' ⟶ X) (fX : X ⟶ Spec (.of k))
  (fX' : X' ⟶ Spec (.of k)) (fX'' : X'' ⟶ Spec (.of k))

/-- **The pullback `g'^* : H^q(X, Ω^p_{X/k}) ⟶ H^q(X', Ω^p_{X'/k})`** along a morphism `g'` of
schemes over `k`, as a `k`-linear map. -/
def hodgeComponentPullbackOverField (w : g' ≫ fX = fX' ≫ 𝟙 _) (p : ℕ) (q : ℤ) :
    hodgeCohomologyComponent (formsAlgebras fX) p q →ₗ[k]
      hodgeCohomologyComponent (formsAlgebras fX') p q where
  toFun := hodgePullback g' fX' fX (𝟙 _) w p q
  map_add' := map_add _
  map_smul' c x := by
    refine ((hodgePullback g' fX' fX (𝟙 _) w p q).map_smulₛₗ (hodgeScalarsOverField fX c) x).trans
      ?_
    exact congrArg (· • _) (RingHom.congr_fun (hodgeBaseRingHom_comp_hodgeScalars g'
      (specScalars k) fX fX' w) c)

/-- The pullback `g'^*` agrees with `hodgePullback` on each class. -/
theorem hodgeComponentPullbackOverField_apply (w : g' ≫ fX = fX' ≫ 𝟙 _) (p : ℕ) (q : ℤ)
    (x : hodgeCohomologyComponent (formsAlgebras fX) p q) :
    hodgeComponentPullbackOverField g' fX fX' w p q x = hodgePullback g' fX' fX (𝟙 _) w p q x :=
  rfl

/-- The pullback depends on the morphism only through the morphism itself. -/
theorem hodgeComponentPullbackOverField_congr {g₁ g₂ : X' ⟶ X} (hg : g₁ = g₂)
    (w₁ : g₁ ≫ fX = fX' ≫ 𝟙 _) (w₂ : g₂ ≫ fX = fX' ≫ 𝟙 _) (p : ℕ) (q : ℤ) :
    hodgeComponentPullbackOverField g₁ fX fX' w₁ p q =
      hodgeComponentPullbackOverField g₂ fX fX' w₂ p q := by
  subst hg
  rfl

/-- The identity induces the identity: `(𝟙 X)^* = id`. -/
theorem hodgeComponentPullbackOverField_id (w : 𝟙 X ≫ fX = fX ≫ 𝟙 _) (p : ℕ) (q : ℤ) :
    hodgeComponentPullbackOverField (𝟙 X) fX fX w p q = LinearMap.id :=
  LinearMap.ext fun x => hodgePullback_id fX w p q x

/-- Composites induce composites: `(g'' ≫ g')^* = g''^* ∘ g'^*`. -/
theorem hodgeComponentPullbackOverField_comp (g'' : X'' ⟶ X') (w : g' ≫ fX = fX' ≫ 𝟙 _)
    (w' : g'' ≫ fX' = fX'' ≫ 𝟙 _) (w'' : (g'' ≫ g') ≫ fX = fX'' ≫ 𝟙 _) (p : ℕ) (q : ℤ)
    (x : hodgeCohomologyComponent (formsAlgebras fX) p q) :
    hodgeComponentPullbackOverField (g'' ≫ g') fX fX'' w'' p q x =
      hodgeComponentPullbackOverField g'' fX' fX'' w' p q
        (hodgeComponentPullbackOverField g' fX fX' w p q x) :=
  hodgePullback_comp_overBase g' fX fX' fX'' g'' w w' w'' p q x

/-- The square of the inverse of an isomorphism `e : X' ≅ X` of schemes over `k`. -/
theorem hodgeSquare_iso_inv (e : X' ≅ X) (w : e.hom ≫ fX = fX' ≫ 𝟙 _) :
    e.inv ≫ fX' = fX ≫ 𝟙 _ := by
  rw [Category.comp_id] at w ⊢
  rw [← w, Iso.inv_hom_id_assoc]

/-- Pulling back along the inverse of an isomorphism and then along the isomorphism is the
identity. -/
theorem hodgeComponentPullbackOverField_hom_comp_inv (e : X' ≅ X) (w : e.hom ≫ fX = fX' ≫ 𝟙 _)
    (w' : e.inv ≫ fX' = fX ≫ 𝟙 _) (p : ℕ) (q : ℤ) :
    hodgeComponentPullbackOverField e.hom fX fX' w p q ∘ₗ
        hodgeComponentPullbackOverField e.inv fX' fX w' p q = LinearMap.id := by
  have w'' : (e.hom ≫ e.inv) ≫ fX' = fX' ≫ 𝟙 _ := by
    rw [Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  have w₀ : 𝟙 X' ≫ fX' = fX' ≫ 𝟙 _ := by rw [Category.id_comp, Category.comp_id]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, ← hodgeComponentPullbackOverField_comp e.inv fX' fX fX' e.hom w' w w'',
    hodgeComponentPullbackOverField_congr fX' fX' e.hom_inv_id w'' w₀,
    hodgeComponentPullbackOverField_id]

/-- **The pullback along an isomorphism of `k`-schemes** `e : X' ≅ X` is a `k`-linear
equivalence `H^q(X, Ω^p_{X/k}) ≅ H^q(X', Ω^p_{X'/k})`, with inverse the pullback along
`e⁻¹`. -/
def hodgeComponentPullbackOverFieldEquiv (e : X' ≅ X) (w : e.hom ≫ fX = fX' ≫ 𝟙 _) (p : ℕ)
    (q : ℤ) :
    hodgeCohomologyComponent (formsAlgebras fX) p q ≃ₗ[k]
      hodgeCohomologyComponent (formsAlgebras fX') p q :=
  LinearEquiv.ofLinearMap (hodgeComponentPullbackOverField e.hom fX fX' w p q)
    (hodgeComponentPullbackOverField e.inv fX' fX (hodgeSquare_iso_inv fX fX' e w) p q)
    (hodgeComponentPullbackOverField_hom_comp_inv fX fX' e w _ p q)
    (hodgeComponentPullbackOverField_hom_comp_inv fX' fX e.symm
      (hodgeSquare_iso_inv fX fX' e w) w p q)

/-- The pullback equivalence along `e` acts as the pullback along `e.hom`. -/
theorem hodgeComponentPullbackOverFieldEquiv_apply (e : X' ≅ X) (w : e.hom ≫ fX = fX' ≫ 𝟙 _)
    (p : ℕ) (q : ℤ) (x : hodgeCohomologyComponent (formsAlgebras fX) p q) :
    hodgeComponentPullbackOverFieldEquiv fX fX' e w p q x =
      hodgeComponentPullbackOverField e.hom fX fX' w p q x :=
  rfl

end Pullback

/-! ### Reading a class in an equal bidegree -/

section Cast

variable {Z Z' : Scheme.{u}} (fZ : Z ⟶ Spec (.of k))

/-- A class of `H^q(Z, Ω^p_{Z/k})` read in an equal bidegree, `k`-linearly. -/
def hodgeComponentCastOverField {pq rs : ℕ × ℕ} (h : pq = rs) :
    hodgeCohomologyComponent (formsAlgebras fZ) pq.1 (pq.2 : ℤ) →ₗ[k]
      hodgeCohomologyComponent (formsAlgebras fZ) rs.1 (rs.2 : ℤ) := by
  subst h
  exact LinearMap.id

/-- Reading a class in the same bidegree is the identity. -/
@[simp]
theorem hodgeComponentCastOverField_rfl (pq : ℕ × ℕ) :
    hodgeComponentCastOverField fZ (rfl : pq = pq) = LinearMap.id :=
  rfl

/-- Reading in an equal bidegree commutes with pullback. -/
theorem hodgeComponentPullbackOverField_hodgeComponentCastOverField (g' : Z' ⟶ Z)
    (fZ' : Z' ⟶ Spec (.of k)) (w : g' ≫ fZ = fZ' ≫ 𝟙 _) {pq rs : ℕ × ℕ} (h : pq = rs)
    (x : hodgeCohomologyComponent (formsAlgebras fZ) pq.1 (pq.2 : ℤ)) :
    hodgeComponentPullbackOverField g' fZ fZ' w rs.1 (rs.2 : ℤ)
        (hodgeComponentCastOverField fZ h x) =
      hodgeComponentCastOverField fZ' h (hodgeComponentPullbackOverField g' fZ fZ' w pq.1 _ x) := by
  subst h
  rfl

end Cast

/-! ### The Künneth map in each bidegree -/

section Kunneth

variable {X Y P P' : Scheme.{u}} (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
  (fP : P ⟶ Spec (.of k)) (p : P ⟶ X) (q : P ⟶ Y) (wp : p ≫ fX = fP ≫ 𝟙 _)
  (wq : q ≫ fY = fP ≫ 𝟙 _)

/-- **The external cup product** `H^b(X, Ω^a) × H^d(Y, Ω^c) ⟶ H^{b + d}(P, Ω^{a + c})`,
`(ξ, ζ) ↦ p^*ξ ∪ q^*ζ`, for morphisms `p : P ⟶ X` and `q : P ⟶ Y` of `k`-schemes, as a
`k`-bilinear map. -/
def hodgeSchemeExternalCup (ab cd : ℕ × ℕ) :
    hodgeCohomologyComponent (formsAlgebras fX) ab.1 (ab.2 : ℤ) →ₗ[k]
      hodgeCohomologyComponent (formsAlgebras fY) cd.1 (cd.2 : ℤ) →ₗ[k]
        hodgeCohomologyComponent (formsAlgebras fP) (ab.1 + cd.1) ((ab.2 + cd.2 : ℕ) : ℤ) :=
  LinearMap.mk₂ k (fun ξ ζ => reindexHodgeDeg (formsAlgebras fP) (Nat.cast_add ab.2 cd.2).symm
      (hodgeCohomologyCup (formsAlgebras fP) ab.1 cd.1 (ab.2 : ℤ) (cd.2 : ℤ)
        (hodgeComponentPullbackOverField p fX fP wp ab.1 (ab.2 : ℤ) ξ)
        (hodgeComponentPullbackOverField q fY fP wq cd.1 (cd.2 : ℤ) ζ)))
    (fun ξ ξ' ζ => by
      rw [map_add, hodgeCupProduct_add_left, reindexHodgeDeg_add])
    (fun c ξ ζ => by
      rw [map_smul, hodgeComponent_smul_def, hodgeCohomologyCup_smul_left, reindexHodgeDeg_smul]
      rfl)
    (fun ξ ζ ζ' => by
      rw [map_add, hodgeCupProduct_add_right, reindexHodgeDeg_add])
    (fun c ξ ζ => by
      rw [map_smul, hodgeComponent_smul_def, hodgeCohomologyCup_smul_right, reindexHodgeDeg_smul]
      rfl)

/-- The external cup product sends `(ξ, ζ)` to `p^*ξ ∪ q^*ζ`, reindexed to bidegree
`(a + c, b + d)`. -/
theorem hodgeSchemeExternalCup_apply (ab cd : ℕ × ℕ)
    (ξ : hodgeCohomologyComponent (formsAlgebras fX) ab.1 (ab.2 : ℤ))
    (ζ : hodgeCohomologyComponent (formsAlgebras fY) cd.1 (cd.2 : ℤ)) :
    hodgeSchemeExternalCup fX fY fP p q wp wq ab cd ξ ζ =
      reindexHodgeDeg (formsAlgebras fP) (Nat.cast_add ab.2 cd.2).symm
        (hodgeCohomologyCup (formsAlgebras fP) ab.1 cd.1 (ab.2 : ℤ) (cd.2 : ℤ)
          (hodgePullback p fP fX (𝟙 _) wp ab.1 (ab.2 : ℤ) ξ)
          (hodgePullback q fP fY (𝟙 _) wq cd.1 (cd.2 : ℤ) ζ)) :=
  rfl

/-- **The Künneth map in bidegree `(r, s)`** for a `k`-scheme `fP : P ⟶ Spec k` with morphisms
`p : P ⟶ X` and `q : P ⟶ Y` over `k`:
`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(P, Ω^r_{P/k})`,
`ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`. -/
def hodgeKunnethBidegreeMapOfSquares (rs : ℕ × ℕ) :
    (DirectSum {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} fun x =>
      hodgeCohomologyComponent (formsAlgebras fX) x.1.1.1 (x.1.1.2 : ℤ) ⊗[k]
        hodgeCohomologyComponent (formsAlgebras fY) x.1.2.1 (x.1.2.2 : ℤ)) →ₗ[k]
      hodgeCohomologyComponent (formsAlgebras fP) rs.1 (rs.2 : ℤ) :=
  DirectSum.toModule k _ _ fun x =>
    hodgeComponentCastOverField fP x.2 ∘ₗ
      TensorProduct.lift (hodgeSchemeExternalCup fX fY fP p q wp wq x.1.1 x.1.2)

/-- The Künneth map on a pure tensor of a summand is the external cup product, read in the
bidegree `(r, s)`. -/
theorem hodgeKunnethBidegreeMapOfSquares_lof_tmul (rs : ℕ × ℕ)
    (x : {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs})
    (ξ : hodgeCohomologyComponent (formsAlgebras fX) x.1.1.1 (x.1.1.2 : ℤ))
    (ζ : hodgeCohomologyComponent (formsAlgebras fY) x.1.2.1 (x.1.2.2 : ℤ)) :
    hodgeKunnethBidegreeMapOfSquares fX fY fP p q wp wq rs
        (DirectSum.lof k {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs}
          (fun x => hodgeCohomologyComponent (formsAlgebras fX) x.1.1.1 (x.1.1.2 : ℤ) ⊗[k]
            hodgeCohomologyComponent (formsAlgebras fY) x.1.2.1 (x.1.2.2 : ℤ)) x (ξ ⊗ₜ ζ)) =
      hodgeComponentCastOverField fP x.2
        (hodgeSchemeExternalCup fX fY fP p q wp wq x.1.1 x.1.2 ξ ζ) := by
  rw [hodgeKunnethBidegreeMapOfSquares, DirectSum.toModule_lof]
  rfl

/-- **Naturality of the external cup product in `P`**: precomposing `p` and `q` with a morphism
`e : P' ⟶ P` of `k`-schemes composes the external cup product with `e^*`. -/
theorem hodgeSchemeExternalCup_comp (fP' : P' ⟶ Spec (.of k)) (e : P' ⟶ P)
    (we : e ≫ fP = fP' ≫ 𝟙 _) (wp' : (e ≫ p) ≫ fX = fP' ≫ 𝟙 _) (wq' : (e ≫ q) ≫ fY = fP' ≫ 𝟙 _)
    (ab cd : ℕ × ℕ) (ξ : hodgeCohomologyComponent (formsAlgebras fX) ab.1 (ab.2 : ℤ))
    (ζ : hodgeCohomologyComponent (formsAlgebras fY) cd.1 (cd.2 : ℤ)) :
    hodgeSchemeExternalCup fX fY fP' (e ≫ p) (e ≫ q) wp' wq' ab cd ξ ζ =
      hodgeComponentPullbackOverField e fP fP' we _ _
        (hodgeSchemeExternalCup fX fY fP p q wp wq ab cd ξ ζ) := by
  rw [hodgeSchemeExternalCup_apply, hodgeSchemeExternalCup_apply,
    hodgeComponentPullbackOverField_apply, hodgePullback_reindexHodgeDeg,
    hodgePullback_hodgeCohomologyCup, hodgePullback_comp_overBase p fX fP fP' e wp we wp',
    hodgePullback_comp_overBase q fY fP fP' e wq we wq']

/-- **Naturality of the Künneth map in `P`**: precomposing `p` and `q` with a morphism
`e : P' ⟶ P` of `k`-schemes composes the Künneth map with `e^*`. -/
theorem hodgeKunnethBidegreeMapOfSquares_comp (fP' : P' ⟶ Spec (.of k)) (e : P' ⟶ P)
    (we : e ≫ fP = fP' ≫ 𝟙 _) (wp' : (e ≫ p) ≫ fX = fP' ≫ 𝟙 _) (wq' : (e ≫ q) ≫ fY = fP' ≫ 𝟙 _)
    (rs : ℕ × ℕ) :
    hodgeKunnethBidegreeMapOfSquares fX fY fP' (e ≫ p) (e ≫ q) wp' wq' rs =
      hodgeComponentPullbackOverField e fP fP' we rs.1 (rs.2 : ℤ) ∘ₗ
        hodgeKunnethBidegreeMapOfSquares fX fY fP p q wp wq rs := by
  refine DirectSum.linearMap_ext k fun x => TensorProduct.ext' fun ξ ζ => ?_
  obtain ⟨⟨ab, cd⟩, hx⟩ := x
  subst hx
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    hodgeKunnethBidegreeMapOfSquares_lof_tmul, hodgeKunnethBidegreeMapOfSquares_lof_tmul]
  exact hodgeSchemeExternalCup_comp fX fY fP p q wp wq fP' e we wp' wq' ab cd ξ ζ

/-- Bijectivity of the Künneth map is unchanged by replacing the structure morphism of `P` and
the morphisms `p`, `q` by equal ones. -/
theorem bijective_hodgeKunnethBidegreeMapOfSquares_congr {fP₁ fP₂ : P ⟶ Spec (.of k)}
    {p₁ p₂ : P ⟶ X} {q₁ q₂ : P ⟶ Y} (hf : fP₁ = fP₂) (hp : p₁ = p₂) (hq : q₁ = q₂)
    (wp₁ : p₁ ≫ fX = fP₁ ≫ 𝟙 _) (wq₁ : q₁ ≫ fY = fP₁ ≫ 𝟙 _) (wp₂ : p₂ ≫ fX = fP₂ ≫ 𝟙 _)
    (wq₂ : q₂ ≫ fY = fP₂ ≫ 𝟙 _) (rs : ℕ × ℕ) :
    Function.Bijective (hodgeKunnethBidegreeMapOfSquares fX fY fP₁ p₁ q₁ wp₁ wq₁ rs) ↔
      Function.Bijective (hodgeKunnethBidegreeMapOfSquares fX fY fP₂ p₂ q₂ wp₂ wq₂ rs) := by
  subst hf hp hq
  rfl

/-- **The Künneth map of axiom (A5) in bidegree `(r, s)`** for smooth projective `k`-schemes is
the Künneth map of their structure morphisms and underlying morphisms of schemes. -/
theorem hodgeKunnethBidegreeMap_eq_hodgeKunnethBidegreeMapOfSquares
    {X Y P : (SmoothProjectiveScheme k).FullSubcategory} (p : P ⟶ X) (q : P ⟶ Y) (rs : ℕ × ℕ) :
    hodgeKunnethBidegreeMap p q rs =
      hodgeKunnethBidegreeMapOfSquares X.obj.hom Y.obj.hom P.obj.hom p.hom.left q.hom.left
        (hodgeSquare_w p) (hodgeSquare_w q) rs :=
  rfl

variable {fX fY p q} in
/-- The square `q ≫ g = (p ≫ f) ≫ 𝟙` of `q` over `Spec k`, for `P` a `k`-scheme through
`p ≫ f`. -/
theorem hodgeSchemeSquare_snd (h : p ≫ fX = q ≫ fY) :
    q ≫ fY = (p ≫ fX) ≫ 𝟙 _ := by
  rw [Category.comp_id, h]

/-- **The Künneth map in bidegree `(r, s)`** for `k`-schemes `f : X ⟶ Spec k`,
`g : Y ⟶ Spec k` and morphisms `p : P ⟶ X`, `q : P ⟶ Y` with `p ≫ f = q ≫ g`, `P` being a
`k`-scheme through `p ≫ f`:
`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(P, Ω^r_{P/k})`,
`ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`. -/
def hodgeSchemeKunnethMap (h : p ≫ fX = q ≫ fY) (rs : ℕ × ℕ) :
    (DirectSum {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs} fun x =>
      hodgeCohomologyComponent (formsAlgebras fX) x.1.1.1 (x.1.1.2 : ℤ) ⊗[k]
        hodgeCohomologyComponent (formsAlgebras fY) x.1.2.1 (x.1.2.2 : ℤ)) →ₗ[k]
      hodgeCohomologyComponent (formsAlgebras (p ≫ fX)) rs.1 (rs.2 : ℤ) :=
  hodgeKunnethBidegreeMapOfSquares fX fY (p ≫ fX) p q (Category.comp_id _).symm
    (hodgeSchemeSquare_snd h) rs

/-- The Künneth map on a pure tensor `ξ ⊗ ζ` of the summand of bidegrees `(a, b)` and `(c, d)`
is `p^*ξ ∪ q^*ζ`, in bidegree `(a + c, b + d)`. -/
theorem hodgeSchemeKunnethMap_lof_tmul (h : p ≫ fX = q ≫ fY) (ab cd : ℕ × ℕ)
    (ξ : hodgeCohomologyComponent (formsAlgebras fX) ab.1 (ab.2 : ℤ))
    (ζ : hodgeCohomologyComponent (formsAlgebras fY) cd.1 (cd.2 : ℤ)) :
    hodgeSchemeKunnethMap fX fY p q h (hodgeBidegreeAdd (ab, cd))
        (DirectSum.lof k {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = hodgeBidegreeAdd (ab, cd)}
          (fun x => hodgeCohomologyComponent (formsAlgebras fX) x.1.1.1 (x.1.1.2 : ℤ) ⊗[k]
            hodgeCohomologyComponent (formsAlgebras fY) x.1.2.1 (x.1.2.2 : ℤ)) ⟨(ab, cd), rfl⟩
          (ξ ⊗ₜ ζ)) =
      reindexHodgeDeg (formsAlgebras (p ≫ fX)) (Nat.cast_add ab.2 cd.2).symm
        (hodgeCohomologyCup (formsAlgebras (p ≫ fX)) ab.1 cd.1 (ab.2 : ℤ) (cd.2 : ℤ)
          (hodgePullback p (p ≫ fX) fX (𝟙 _) (Category.comp_id _).symm ab.1 (ab.2 : ℤ) ξ)
          (hodgePullback q (p ≫ fX) fY (𝟙 _) (hodgeSchemeSquare_snd h) cd.1 (cd.2 : ℤ) ζ)) :=
  hodgeKunnethBidegreeMapOfSquares_lof_tmul fX fY (p ≫ fX) p q _ _ _ ⟨(ab, cd), rfl⟩ ξ ζ

/-- **Bijectivity of the Künneth map is invariant under isomorphism**: for an isomorphism
`e : P' ≅ P` of schemes, the Künneth map of `e ≫ p` and `e ≫ q` is bijective if and only if that
of `p` and `q` is. -/
theorem bijective_hodgeSchemeKunnethMap_iso_iff (h : p ≫ fX = q ≫ fY) (e : P' ≅ P)
    (rs : ℕ × ℕ) :
    Function.Bijective (hodgeSchemeKunnethMap fX fY (e.hom ≫ p) (e.hom ≫ q)
        (by rw [Category.assoc, Category.assoc, h]) rs) ↔
      Function.Bijective (hodgeSchemeKunnethMap fX fY p q h rs) := by
  have we : e.hom ≫ (p ≫ fX) = ((e.hom ≫ p) ≫ fX) ≫ 𝟙 _ := by
    rw [Category.comp_id, Category.assoc]
  have hcomp := hodgeKunnethBidegreeMapOfSquares_comp fX fY (p ≫ fX) p q
    (Category.comp_id _).symm (hodgeSchemeSquare_snd h) ((e.hom ≫ p) ≫ fX) e.hom we
    (Category.comp_id _).symm (hodgeSchemeSquare_snd (by rw [Category.assoc, Category.assoc, h]))
    rs
  change Function.Bijective (hodgeKunnethBidegreeMapOfSquares fX fY ((e.hom ≫ p) ≫ fX)
    (e.hom ≫ p) (e.hom ≫ q) _ _ rs) ↔ _
  rw [hcomp, LinearMap.coe_comp]
  exact Function.Bijective.of_comp_iff' (hodgeComponentPullbackOverFieldEquiv (p ≫ fX)
    ((e.hom ≫ p) ≫ fX) e we rs.1 (rs.2 : ℤ)).bijective _

end Kunneth

/-! ### Reduction to the chosen fibre product -/

/-- **The Künneth map of any fibre product reduces to the chosen one**: for smooth projective `X`,
`Y` over `k`, if in bidegree `(r, s)` the Künneth map
`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(X ×_k Y, Ω^r)` of the
chosen pullback `X ×_k Y` with its two projections is bijective, then so is the Künneth map
`hodgeKunnethBidegreeMap p q (r, s)` of every fibre product `P` of `X` and `Y` over `Spec k` with
projections `p` and `q`. -/
theorem bijective_hodgeKunnethBidegreeMap_of_pullback
    {X Y P : (SmoothProjectiveScheme k).FullSubcategory} (p : P ⟶ X) (q : P ⟶ Y)
    (hP : IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom Y.obj.hom) (rs : ℕ × ℕ)
    (H : Function.Bijective (hodgeSchemeKunnethMap X.obj.hom Y.obj.hom
        (pullback.fst X.obj.hom Y.obj.hom) (pullback.snd X.obj.hom Y.obj.hom) pullback.condition
          rs)) :
    Function.Bijective (hodgeKunnethBidegreeMap p q rs) := by
  have h1 := (bijective_hodgeSchemeKunnethMap_iso_iff X.obj.hom Y.obj.hom
    (pullback.fst X.obj.hom Y.obj.hom) (pullback.snd X.obj.hom Y.obj.hom) pullback.condition
    hP.isoPullback rs).2 H
  rw [hodgeKunnethBidegreeMap_eq_hodgeKunnethBidegreeMapOfSquares]
  refine (bijective_hodgeKunnethBidegreeMapOfSquares_congr X.obj.hom Y.obj.hom ?_
    hP.isoPullback_hom_fst hP.isoPullback_hom_snd _ _ _ _ rs).1 h1
  rw [hP.isoPullback_hom_fst]
  exact Over.w p.hom

end Stacks.HodgeWeil

end
