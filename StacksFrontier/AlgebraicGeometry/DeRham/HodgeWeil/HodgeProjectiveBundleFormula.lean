module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeLerayHirschIso
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeDGAComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.ProjectiveBundleLocalTrivial
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FirstChernClassPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeProjectiveBundleAxiom

/-!
# The projective bundle formula for Hodge cohomology

Let `k` be a field, `s : X ⟶ Spec k` a scheme over `k`, `ℰ` a finite locally free `𝒪_X`-module
of rank `r + 1`, `p : P = 𝐏(ℰ) ⟶ X` its projective bundle and
`ξ = c₁^{Hodge}(𝒪_P(1)) ∈ H^1(P, Ω^1_{P/k}) ⊂ H^2_{Hodge}(P/k)`. The projective bundle formula
for Hodge cohomology says that for every `n` the map
`∏_{i ≤ r} H^{n - 2i}_{Hodge}(X/k) ⟶ H^n_{Hodge}(P/k)`, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)`
is bijective. This file deduces it from the same statement for the trivial bundles
`ℙʳ_k ×_k V ⟶ V` over affine `k`-schemes `V`, by the argument of [Stacks, Tag 0FMT] run on the
Hodge complex `ℋ = ⨁_q Ω^q[-q]`:

* by Proposition 0FMR for `ℋ` (`Stacks.HodgeWeil.bijective_sum_dgaCohomologyCup_of_isBasis`) it
  suffices that the formula holds over the members `V` of a basis of `X`, for the restriction
  `p⁻¹V ⟶ V` and the restricted classes, over the open `⊤` of `Spec k`;
* the affine opens `V` inside an open on which `ℰ` is free form a basis, and over such `V` the
  open `p⁻¹V` is `ℙʳ_k ×_k V`, with `𝒪_P(1)` restricting to the pullback of `𝒪(1)`
  (`Stacks.HodgeWeil.exists_isPullback_bundleProj_restrict`);
* pullback along an isomorphism over an isomorphism of bases is bijective on Hodge cohomology and
  compatible with cup products, and the Hodge first Chern class commutes with pullback, so the
  formula for `p⁻¹V ⟶ V` over `⊤` is the formula for `ℙʳ_k ×_k V ⟶ V` over `Spec k`.

The cohomology of `ℋ`, on which Proposition 0FMR is stated, is identified with Hodge cohomology by
`Stacks.HodgeWeil.hodgeDgaEquiv`, compatibly with cup products and pullbacks; the graded algebra
`H^*_{Hodge}`, on which the formula is stated, is identified degree by degree with the groups
`H^m_{Hodge}`.

## Main definitions

* `Stacks.HodgeWeil.hodgeLerayHirschSum`: the map `(a_i) ↦ ∑ ξ_i ∪ p^*a_i` on the groups
  `H^m_{Hodge}`.
* `Stacks.HodgeWeil.toHodgeGrade`: a class of `H^m_{Hodge}` as an element of the degree-`m` part
  of `H^*_{Hodge}`.

## Main results

* `Stacks.HodgeWeil.bijective_hodgePiecePullback_of_isIso`: a square of isomorphisms induces a
  bijection on `H^n_{Hodge}`.
* `Stacks.HodgeWeil.bijective_hodgeLerayHirschSum_iff_of_isIso`,
  `Stacks.HodgeWeil.bijective_hodgeLerayHirschSum_pow_of_isIso`: the map
  `(a_i) ↦ ∑ ξ_i ∪ p^*a_i` is invariant under isomorphisms.
* `Stacks.HodgeWeil.bijective_sum_dgaCohomologyCup_iff`: the map on the cohomology of the Hodge
  complexes is bijective if and only if it is so on Hodge cohomology.
* `Stacks.HodgeWeil.bijective_degreewiseMap_iff`: the degreewise map of the graded algebras is
  bijective if and only if it is so on the groups `H^m_{Hodge}`.
* `Stacks.HodgeWeil.hodgeAlgebraPullback_hodgeFirstChernClass_eq`: pullbacks of Hodge first Chern
  classes agree when the Picard classes do.
* `Stacks.HodgeWeil.bijective_hodgeLerayHirschSum_restrict_of_trivial`: the formula over an affine
  open on which `ℰ` is free.
* `Stacks.HodgeWeil.bijective_degreewiseMap_bundle_of_trivial`: **the projective bundle formula
  for Hodge cohomology**, from the formula for trivial bundles over affine bases;
  `Stacks.HodgeWeil.bijective_degreewiseMap_hodgeBundleClass_of_trivial` is the same statement
  for `𝐏(ℰ)` formed from any proof that `ℰ` is finite locally free.

## Implementation notes

The formula for the trivial bundles `ℙʳ_k ×_k V ⟶ V`, `V` affine, is a hypothesis of the main
results: it is the case of the Künneth formula for `ℙʳ_k × V` together with the Hodge cohomology
of `ℙʳ_k`, and the results here are the reduction of the general case to it.

The restriction of `P ⟶ X ⟶ Spec k` to `V ⊆ X` lives over the open subscheme `⊤` of `Spec k`;
its inclusion `⊤ ⟶ Spec k` is an isomorphism, and the comparison is pullback along the square of
isomorphisms `(p⁻¹V ≅ ℙʳ_k ×_k V, ⊤ ≅ Spec k)`.

The classes `ξ_i` of the formula are the components of degree `2i` of the powers `ξ^i` in
`H^*_{Hodge}`; pullback commutes with taking components and powers since it is a ring
homomorphism of graded rings.

## References

* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.SheafOfModules (dgaCohomology hodgeCohomologyComponent)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.HodgeWeil

/-- If `A ∘ F = G ∘ (fun x i => b i (x i))` with `A` and every `b i` bijective, then `F` is
bijective if and only if `G` is. -/
private theorem bijective_iff_of_comp_eq_pi {ι : Type*} {X Y : ι → Type*} {α β : Type*}
    {F : (∀ i, X i) → α} {G : (∀ i, Y i) → β} {A : α → β} (b : ∀ i, X i → Y i)
    (hb : ∀ i, Function.Bijective (b i)) (hA : Function.Bijective A)
    (h : A ∘ F = G ∘ fun x i => b i (x i)) : Function.Bijective F ↔ Function.Bijective G := by
  have hB : Function.Bijective fun (x : ∀ i, X i) i => b i (x i) :=
    (Equiv.piCongrRight fun i => Equiv.ofBijective _ (hb i)).bijective
  rw [← Function.Bijective.of_comp_iff' hA, h]
  exact Function.Bijective.of_comp_iff _ hB

/-! ### Pullback on `H^n_{Hodge}` -/

section Pullback

variable {X X' S S' : Scheme.{u}}

/-- The pullback on `H^n_{Hodge}` depends on the two horizontal morphisms of the square only
through the morphisms themselves. -/
theorem hodgePiecePullback_congr {g'₁ g'₂ : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g₁ g₂ : S' ⟶ S}
    (h' : g'₁ = g'₂) (h : g₁ = g₂) (w₁ : g'₁ ≫ f = f' ≫ g₁) (w₂ : g'₂ ≫ f = f' ≫ g₂) (n : ℤ)
    (x : hodgePiece (formsAlgebras f) n) :
    hodgePiecePullback g'₁ f' f g₁ w₁ n x = hodgePiecePullback g'₂ f' f g₂ w₂ n x := by
  subst h' h
  rfl

variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g)

/-- **A square of isomorphisms induces a bijection on `H^n_{Hodge}`**: if both horizontal
morphisms of the square are isomorphisms, the pullback along the inverse square is inverse to
the pullback. -/
theorem bijective_hodgePiecePullback_of_isIso [IsIso g'] [IsIso g] (n : ℤ) :
    Function.Bijective (hodgePiecePullback g' f' f g w n) := by
  have w' : inv g' ≫ f' = f ≫ inv g := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← w, IsIso.inv_hom_id_assoc]
  refine Function.bijective_iff_has_inverse.2
    ⟨hodgePiecePullback (inv g') f f' (inv g) w' n, fun x => ?_, fun x => ?_⟩
  · have w₁ : (inv g' ≫ g') ≫ f = f ≫ (inv g ≫ g) := by simp
    rw [← hodgePiecePullback_comp g' f' f g w (inv g') f (inv g) w' w₁ n x,
      hodgePiecePullback_congr (IsIso.inv_hom_id g') (IsIso.inv_hom_id g) w₁ (by simp) n x,
      hodgePiecePullback_id]
  · have w₂ : (g' ≫ inv g') ≫ f' = f' ≫ (g ≫ inv g) := by simp
    rw [← hodgePiecePullback_comp (inv g') f f' (inv g) w' g' f' g w w₂ n x,
      hodgePiecePullback_congr (IsIso.hom_inv_id g') (IsIso.hom_inv_id g) w₂ (by simp) n x,
      hodgePiecePullback_id]

/-- The pullback on `H^n_{Hodge}` commutes with reading a class in an equal degree. -/
theorem hodgePiecePullback_castHodgePiece {n n' : ℤ} (h : n = n')
    (x : hodgePiece (formsAlgebras f) n) :
    hodgePiecePullback g' f' f g w n' (castHodgePiece (formsAlgebras f) h x) =
      castHodgePiece (formsAlgebras f') h (hodgePiecePullback g' f' f g w n x) := by
  subst h
  rfl

/-- **The pullback on `H^*_{Hodge}` is the pullback on each `H^n_{Hodge}`**: the component of
degree `n` of `g'^*a` is `g'^*` of the component of degree `n` of `a`. -/
theorem hodgeAlgebraPullback_apply_degree (a : hodgeAlgebra (formsAlgebras f)) (n : ℤ) :
    hodgeAlgebraPullback g' f' f g w a n = hodgePiecePullback g' f' f g w n (a n) := by
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  | of j x =>
    rw [hodgeAlgebraPullback_of]
    by_cases h : n = j
    · subst h
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ h, DirectSum.of_eq_of_ne _ _ _ h, map_zero]
  | add a b ha hb => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, ha, hb, map_add]

end Pullback

/-! ### The map `(a_i) ↦ ∑ ξ_i ∪ p^*a_i` on `H^*_{Hodge}` -/

section LerayHirschSum

variable {P Y S : Scheme.{u}} (p : P ⟶ Y) (πY : Y ⟶ S) (πP : P ⟶ S) (w : p ≫ πY = πP ≫ 𝟙 S)

/-- **The map `⨁_i H^{k - n_i}_{Hodge}(Y/S) ⟶ H^k_{Hodge}(P/S)`, `(a_i) ↦ ∑ ξ_i ∪ p^*a_i`**, for
a morphism `p : P ⟶ Y` of `S`-schemes and classes `ξ_i ∈ H^{n_i}_{Hodge}(P/S)`. -/
def hodgeLerayHirschSum {N : ℕ} (n : Fin N → ℕ) (ξ : ∀ i, hodgePiece (formsAlgebras πP) (n i))
    (k : ℤ) (a : ∀ i, hodgePiece (formsAlgebras πY) (k - n i)) :
    hodgePiece (formsAlgebras πP) k :=
  ∑ i, castHodgePiece (formsAlgebras πP) (add_sub_cancel (n i : ℤ) k)
    (hodgePieceMul (formsAlgebras πP) (n i) (k - n i) (ξ i)
      (hodgePiecePullback p πP πY (𝟙 S) w (k - n i) (a i)))

variable {P' Y' S' : Scheme.{u}} (p' : P' ⟶ Y') (πY' : Y' ⟶ S') (πP' : P' ⟶ S')
  (w' : p' ≫ πY' = πP' ≫ 𝟙 S') (α : P' ⟶ P) (β : Y' ⟶ Y) (γ : S' ⟶ S)
  (hα : α ≫ πP = πP' ≫ γ) (hβ : β ≫ πY = πY' ≫ γ) (hp : p' ≫ β = α ≫ p)

include hp in
/-- **The map `(a_i) ↦ ∑ ξ_i ∪ p^*a_i` commutes with pullback**: for a morphism of the data
`(P ⟶ Y ⟶ S)` given by `α : P' ⟶ P`, `β : Y' ⟶ Y` over `γ : S' ⟶ S`,
`α^*(∑ ξ_i ∪ p^*a_i) = ∑ α^*ξ_i ∪ p'^*(β^*a_i)`. -/
theorem hodgePiecePullback_hodgeLerayHirschSum {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, hodgePiece (formsAlgebras πP) (n i)) (k : ℤ)
    (a : ∀ i, hodgePiece (formsAlgebras πY) (k - n i)) :
    hodgePiecePullback α πP' πP γ hα k (hodgeLerayHirschSum p πY πP w n ξ k a) =
      hodgeLerayHirschSum p' πY' πP' w' n (fun i => hodgePiecePullback α πP' πP γ hα (n i) (ξ i))
        k (fun i => hodgePiecePullback β πY' πY γ hβ (k - n i) (a i)) := by
  unfold hodgeLerayHirschSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hodgePiecePullback_castHodgePiece, hodgePiecePullback_mul]
  have w₁ : (α ≫ p) ≫ πY = πP' ≫ (γ ≫ 𝟙 S) := by
    rw [Category.assoc, w, ← Category.assoc, hα, Category.assoc]
  have w₂ : (p' ≫ β) ≫ πY = πP' ≫ (𝟙 S' ≫ γ) := by
    rw [Category.assoc, hβ, ← Category.assoc, w', Category.assoc]
  rw [← hodgePiecePullback_comp p πP πY (𝟙 S) w α πP' γ hα w₁,
    ← hodgePiecePullback_comp β πY' πY γ hβ p' πP' (𝟙 S') w' w₂,
    hodgePiecePullback_congr hp.symm ((Category.comp_id γ).trans (Category.id_comp γ).symm) w₁ w₂]

include hβ hp in
/-- **The map `(a_i) ↦ ∑ ξ_i ∪ p^*a_i` is bijective for `p` if and only if it is so for `p'`**,
when `α`, `β` and `γ` are isomorphisms. -/
theorem bijective_hodgeLerayHirschSum_iff_of_isIso [IsIso α] [IsIso β] [IsIso γ] {N : ℕ}
    (n : Fin N → ℕ) (ξ : ∀ i, hodgePiece (formsAlgebras πP) (n i)) (k : ℤ) :
    Function.Bijective (hodgeLerayHirschSum p πY πP w n ξ k) ↔
      Function.Bijective (hodgeLerayHirschSum p' πY' πP' w' n
        (fun i => hodgePiecePullback α πP' πP γ hα (n i) (ξ i)) k) := by
  have hA := bijective_hodgePiecePullback_of_isIso α πP' πP γ hα k
  exact bijective_iff_of_comp_eq_pi (fun i => hodgePiecePullback β πY' πY γ hβ (k - n i))
    (fun i => bijective_hodgePiecePullback_of_isIso β πY' πY γ hβ (k - n i)) hA
    (funext fun a => hodgePiecePullback_hodgeLerayHirschSum p πY πP w p' πY' πP' w' α β γ hα hβ
      hp n ξ k a)

/-- **Transport of `(a_i) ↦ ∑ ξ^i ∪ p^*a_i` along isomorphisms**: let `α : P' ⟶ P` and
`γ : S' ⟶ S` be isomorphisms, `p' : P' ⟶ Y` over `S'` with `p' = α ≫ p`, and `ι : P' ⟶ P''` over
`γ` with `α^*ξ = ι^*ζ`. If `(a_i) ↦ ∑ ξ^i ∪ p^*a_i` is bijective in degree `k`, then so is
`(a_i) ↦ ∑ (ι^*ζ)^i ∪ p'^*a_i`, the classes being the components of degree `2i` of the powers. -/
theorem bijective_hodgeLerayHirschSum_pow_of_isIso {P Y S P' S' P'' : Scheme.{u}} (p : P ⟶ Y)
    (πY : Y ⟶ S) (πP : P ⟶ S) (w : p ≫ πY = πP ≫ 𝟙 S) (p' : P' ⟶ Y) (πY' : Y ⟶ S')
    (πP' : P' ⟶ S') (w' : p' ≫ πY' = πP' ≫ 𝟙 S') (α : P' ⟶ P) (γ : S' ⟶ S) [IsIso α] [IsIso γ]
    (hα : α ≫ πP = πP' ≫ γ) (hβ : 𝟙 Y ≫ πY = πY' ≫ γ) (hp : p' ≫ 𝟙 Y = α ≫ p) (ι : P' ⟶ P'')
    (πP'' : P'' ⟶ S) (wι : ι ≫ πP'' = πP' ≫ γ) (ξ : hodgeAlgebra (formsAlgebras πP))
    (ζ : hodgeAlgebra (formsAlgebras πP''))
    (hξζ : hodgeAlgebraPullback α πP' πP γ hα ξ = hodgeAlgebraPullback ι πP' πP'' γ wι ζ)
    (N : ℕ) (k : ℤ)
    (h : Function.Bijective (hodgeLerayHirschSum p πY πP w (fun i : Fin N => 2 * (i : ℕ))
      (fun i => (ξ ^ (i : ℕ)) ((2 * (i : ℕ) : ℕ) : ℤ)) k)) :
    Function.Bijective (hodgeLerayHirschSum p' πY' πP' w' (fun i : Fin N => 2 * (i : ℕ))
      (fun i => hodgePiecePullback ι πP' πP'' γ wι _ ((ζ ^ (i : ℕ)) ((2 * (i : ℕ) : ℕ) : ℤ)))
      k) := by
  rw [bijective_hodgeLerayHirschSum_iff_of_isIso p πY πP w p' πY' πP' w' α (𝟙 Y) γ hα hβ hp] at h
  convert h using 3 with i
  rw [← hodgeAlgebraPullback_apply_degree, ← hodgeAlgebraPullback_apply_degree, map_pow, map_pow,
    hξζ]

end LerayHirschSum

/-! ### The cohomology of the Hodge complex and `H^*_{Hodge}` -/

section DGA

/-- `hodgeDgaEquiv` commutes with reading a class in an equal degree. -/
theorem hodgeDgaEquiv_eqToHom {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}
    {φ : A ⟶ X.sheaf}
    (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier)
      (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u} φ))
    {n n' : ℤ} (h : n = n') (x : dgaCohomology (hodgeDGA B) n) :
    hodgeDgaEquiv B n' ((eqToHom (congrArg (dgaCohomology (hodgeDGA B)) h)).hom x) =
      castHodgePiece B h (hodgeDgaEquiv B n x) := by
  subst h
  rfl

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- `hodgeDgaEquiv` carries the pullback `f^*` on the cohomology of the Hodge complexes to the
pullback on `H^m_{Hodge}`. -/
theorem hodgeDgaEquiv_hodgeDgaPullback (m : ℤ)
    (a : dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) m) :
    hodgeDgaEquiv (formsAlgebras (f ≫ g)) m (hodgeDgaPullback f g m a) =
      hodgePiecePullback f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm m
        (hodgeDgaEquiv (formsAlgebras g) m a) :=
  hodgeDgaEquiv_pullback f (f ≫ g) g (𝟙 S) (Category.comp_id _).symm m a

/-- **`hodgeDgaEquiv` carries `(a_i) ↦ ∑ ξ_i ∪ f^*a_i` on the cohomology of the Hodge complexes
to the same map on `H^*_{Hodge}`.** -/
theorem hodgeDgaEquiv_sum_dgaCohomologyCup {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ)) (k : ℤ)
    (a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) (k - n i)) :
    hodgeDgaEquiv (formsAlgebras (f ≫ g)) k
        (∑ i, (eqToHom (congrArg (dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))))
            (add_sub_cancel (n i : ℤ) k))).hom
          (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i) (k - n i)
            (ξ i) (hodgeDgaPullback f g (k - n i) (a i)))) =
      hodgeLerayHirschSum f g (f ≫ g) (Category.comp_id _).symm n
        (fun i => hodgeDgaEquiv (formsAlgebras (f ≫ g)) (n i) (ξ i)) k
        (fun i => hodgeDgaEquiv (formsAlgebras g) (k - n i) (a i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (hodgeDgaEquiv_eqToHom (formsAlgebras (f ≫ g)) (add_sub_cancel (n i : ℤ) k) _).trans ?_
  refine congrArg (castHodgePiece (formsAlgebras (f ≫ g)) (add_sub_cancel (n i : ℤ) k)) ?_
  refine (hodgeDgaEquiv_cup (formsAlgebras (f ≫ g)) (n i) (k - n i) _ _).trans ?_
  exact congrArg (hodgePieceMul (formsAlgebras (f ≫ g)) (n i) (k - n i) _)
    (hodgeDgaEquiv_hodgeDgaPullback f g (k - n i) (a i))

/-- **`(a_i) ↦ ∑ ξ_i ∪ f^*a_i` is bijective on the cohomology of the Hodge complexes if and only
if it is so on `H^*_{Hodge}`**, for the classes `ξ_i` read through `hodgeDgaEquiv`. -/
theorem bijective_sum_dgaCohomologyCup_iff {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ)) (k : ℤ) :
    Function.Bijective
        (fun a : ∀ i, dgaCohomology (hodgeDGA (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
          ∑ i, (eqToHom (congrArg (dgaCohomology (hodgeDGA
              (Scheme.Hom.deRhamAlgebras (f ≫ g)))) (add_sub_cancel (n i : ℤ) k))).hom
            (dgaCohomologyCup (hodgeDGA (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i) (k - n i)
              (ξ i) (hodgeDgaPullback f g (k - n i) (a i)))) ↔
      Function.Bijective (hodgeLerayHirschSum f g (f ≫ g) (Category.comp_id _).symm n
        (fun i => hodgeDgaEquiv (formsAlgebras (f ≫ g)) (n i) (ξ i)) k) := by
  have hA := (hodgeDgaEquiv (formsAlgebras (f ≫ g)) k).bijective
  exact bijective_iff_of_comp_eq_pi (fun i => hodgeDgaEquiv (formsAlgebras g) (k - n i))
    (fun i => (hodgeDgaEquiv (formsAlgebras g) (k - n i)).bijective) hA
    (funext fun a => hodgeDgaEquiv_sum_dgaCohomologyCup f g n ξ k a)

end DGA

/-! ### `H^*_{Hodge}` as a graded algebra -/

section Grade

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier)
    (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u} φ))
  {K : Type*} [CommRing K]
  (σ : K →+* (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤))

/-- A class of `H^m_{Hodge}(X/S)`, as an element of the degree-`m'` part of `H^*_{Hodge}(X/S)`,
for `m = m'`. -/
def toHodgeGrade {m m' : ℤ} (h : m = m') (x : hodgePiece B m) :
    letI := hodgeAlgebraAlgebra B σ
    hodgeGrade B σ m' :=
  letI := hodgeAlgebraAlgebra B σ
  ⟨DirectSum.of (hodgePiece B) m x,
    (mem_hodgeGrade B σ m' _).2 ⟨castHodgePiece B h x, (of_castHodgePiece B h x).symm⟩⟩

/-- The element `toHodgeGrade B σ h x` of `H^*_{Hodge}(X/S)` is the class `x` in degree `m`. -/
theorem coe_toHodgeGrade {m m' : ℤ} (h : m = m') (x : hodgePiece B m) :
    letI := hodgeAlgebraAlgebra B σ
    (toHodgeGrade B σ h x : hodgeAlgebra B) = DirectSum.of (hodgePiece B) m x :=
  rfl

/-- `H^m_{Hodge}(X/S)` is the degree-`m'` part of `H^*_{Hodge}(X/S)`, for `m = m'`. -/
theorem bijective_toHodgeGrade {m m' : ℤ} (h : m = m') :
    Function.Bijective (toHodgeGrade B σ h) := by
  let _ := hodgeAlgebraAlgebra B σ
  subst h
  refine ⟨fun x y hxy => DirectSum.of_injective m (congrArg Subtype.val hxy), fun a => ?_⟩
  obtain ⟨y, hy⟩ := (mem_hodgeGrade B σ m a).1 a.2
  exact ⟨y, Subtype.ext hy.symm⟩

/-- An element of the degree-`m` part of `H^*_{Hodge}(X/S)` is its component of degree `m`. -/
theorem of_apply_eq_of_mem_hodgeGrade {m : ℤ} (a : hodgeAlgebra B)
    (ha : letI := hodgeAlgebraAlgebra B σ; a ∈ hodgeGrade B σ m) :
    DirectSum.of (hodgePiece B) m (a m) = a := by
  obtain ⟨y, rfl⟩ := (mem_hodgeGrade B σ m a).1 ha
  rw [DirectSum.of_eq_same]

end Grade

/-! ### The degreewise map of the projective bundle formula -/

section Degreewise

variable {K : Type*} [Field K] {P Y S : Scheme.{u}} (p : P ⟶ Y) (πY : Y ⟶ S) (πP : P ⟶ S)
  (w : p ≫ πY = πP ≫ 𝟙 S) (τ : K →+* S.sheaf.obj.obj (op ⊤))

/-- **The degreewise map `∏_{i < N} H^{k - 2i}_{Hodge}(Y/S) ⟶ H^k_{Hodge}(P/S)`,
`(a_i) ↦ ∑ ξ^i ∪ p^*a_i`, of the graded algebras is bijective if and only if it is so on the
groups `H^m_{Hodge}`**, for the components `ξ_i` of degree `2i` of `ξ^i`. -/
theorem bijective_degreewiseMap_iff (ξ : hodgeAlgebra (formsAlgebras πP))
    (hξ : letI := hodgeAlgebraAlgebra (formsAlgebras πP) (hodgeScalars τ πP)
      ξ ∈ hodgeGrade (formsAlgebras πP) (hodgeScalars τ πP) 2) (N : ℕ) (k : ℤ) :
    letI := hodgeAlgebraAlgebra (formsAlgebras πY) (hodgeScalars τ πY)
    letI := hodgeAlgebraAlgebra (formsAlgebras πP) (hodgeScalars τ πP)
    letI := hodgeGradedAlgebra (formsAlgebras πY) (hodgeScalars τ πY)
    letI := hodgeGradedAlgebra (formsAlgebras πP) (hodgeScalars τ πP)
    Function.Bijective (Stacks.WeilDeRham.degreewiseMap
        (hodgeGrade (formsAlgebras πY) (hodgeScalars τ πY))
        (hodgeGrade (formsAlgebras πP) (hodgeScalars τ πP))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade p τ πY πP w) hξ N k) ↔
      Function.Bijective (hodgeLerayHirschSum p πY πP w (fun i : Fin N => 2 * (i : ℕ))
        (fun i => (ξ ^ (i : ℕ)) ((2 * (i : ℕ) : ℕ) : ℤ)) k) := by
  let _ := hodgeAlgebraAlgebra (formsAlgebras πY) (hodgeScalars τ πY)
  let _ := hodgeAlgebraAlgebra (formsAlgebras πP) (hodgeScalars τ πP)
  let _ := hodgeGradedAlgebra (formsAlgebras πY) (hodgeScalars τ πY)
  let _ := hodgeGradedAlgebra (formsAlgebras πP) (hodgeScalars τ πP)
  have hdeg : ∀ i : Fin N, k - ((2 * (i : ℕ) : ℕ) : ℤ) = k - 2 * ((i : ℕ) : ℤ) := fun i => by
    push_cast
    ring
  have hmem : ∀ i : Fin N,
      ξ ^ (i : ℕ) ∈ hodgeGrade (formsAlgebras πP) (hodgeScalars τ πP) ((2 * (i : ℕ) : ℕ) : ℤ) :=
    fun i => (show (i : ℕ) • (2 : ℤ) = ((2 * (i : ℕ) : ℕ) : ℤ) by
      rw [nsmul_eq_mul]
      push_cast
      ring) ▸ SetLike.pow_mem_graded (i : ℕ) hξ
  have hA := bijective_toHodgeGrade (formsAlgebras πP) (hodgeScalars τ πP) (rfl : k = k)
  refine Iff.symm (bijective_iff_of_comp_eq_pi
    (fun i => toHodgeGrade (formsAlgebras πY) (hodgeScalars τ πY) (hdeg i))
    (fun i => bijective_toHodgeGrade (formsAlgebras πY) (hodgeScalars τ πY) (hdeg i)) hA ?_)
  funext x
  refine Subtype.ext (Eq.symm ?_)
  rw [Function.comp_apply, Function.comp_apply, Stacks.WeilDeRham.coe_degreewiseMap,
    coe_toHodgeGrade, hodgeLerayHirschSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_toHodgeGrade, hodgeAlgebraPullbackOverBase_apply, hodgeAlgebraPullback_of,
    of_castHodgePiece, ← hodgeAlgebra_of_mul_of,
    of_apply_eq_of_mem_hodgeGrade (formsAlgebras πP) (hodgeScalars τ πP) _ (hmem i)]

end Degreewise

/-! ### The projective bundle formula -/

section Bundle

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open Stacks.ProjectiveBundleDeRham (projectiveTwistOne isInvertible_projectiveTwistOne)
open Stacks.SheafOfModules (pullbackPicardHom pullbackPicardHom_comp_apply)
open Stacks.WeilCohomology (picardClassOf)
open AlgebraicGeometry.DeRhamLerayHirsch (restrictBase_w restrict_w)

variable {k : Type u} [Field k]

/-- **Pullbacks of Hodge first Chern classes agree when the Picard classes do**: for
`ι : P' ⟶ P`, `α : P' ⟶ T` and `q : T ⟶ Q` over a morphism `γ : S' ⟶ S` of bases, and invertible
modules `ℒ` on `P` and `ℳ` on `Q` with `(α ≫ q)^*ℳ = ι^*ℒ` in `Pic(P')`, the classes
`ι^*c₁^{Hodge}(ℒ)` and `α^*q^*c₁^{Hodge}(ℳ)` of `H^2_{Hodge}(P'/S')` agree. -/
theorem hodgeAlgebraPullback_hodgeFirstChernClass_eq {P P' T Q S S' : Scheme.{u}} (ι : P' ⟶ P)
    (α : P' ⟶ T) (q : T ⟶ Q) (πP : P ⟶ S) (πP' : P' ⟶ S') (πT : T ⟶ S) (πQ : Q ⟶ S)
    (γ : S' ⟶ S) (wι : ι ≫ πP = πP' ≫ γ) (wα : α ≫ πT = πP' ≫ γ) (wq : q ≫ πQ = πT ≫ 𝟙 S)
    (L : P.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (M : Q.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Q.presheaf Q.ringCatSheaf.2 M)
    (h : pullbackPicardHom (α ≫ q) (picardClassOf Q M hM) =
      pullbackPicardHom ι (picardClassOf P L hL)) :
    hodgeAlgebraPullback ι πP' πP γ wι (DirectSum.of (hodgePiece (formsAlgebras πP)) 2
        (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
          (hodgeCohomologyComponent (formsAlgebras πP) i.1.1 (i.1.2 : ℤ) : Type u)) bidegreeOneOne
          (hodgeFirstChernClassModule πP (picardClassOf P L hL)))) =
      hodgeAlgebraPullback α πP' πT γ wα (hodgeAlgebraPullback q πT πQ (𝟙 S) wq
        (DirectSum.of (hodgePiece (formsAlgebras πQ)) 2
          (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
            (hodgeCohomologyComponent (formsAlgebras πQ) i.1.1 (i.1.2 : ℤ) : Type u))
            bidegreeOneOne (hodgeFirstChernClassModule πQ (picardClassOf Q M hM))))) := by
  have h₁ := hodgePullback_hodgeFirstChernClassModule_picardClassOf ι πP' πP γ wι L hL
  have h₂ := hodgePullback_hodgeFirstChernClassModule_picardClassOf q πT πQ (𝟙 S) wq M hM
  have h₃ := hodgePullback_hodgeFirstChernClassModule_picardClassOf α πP' πT γ wα
    ((Scheme.Modules.pullback q).obj M) (Stacks.WeilCohomology.isInvertible_pullback_obj q M hM)
  have e₁ := Stacks.ProjectiveBundleFibre.pullbackPicardHom_picardClassOf ι L hL
  have e₂ := Stacks.ProjectiveBundleFibre.pullbackPicardHom_picardClassOf q M hM
  have e₃ := Stacks.ProjectiveBundleFibre.pullbackPicardHom_picardClassOf α
    ((Scheme.Modules.pullback q).obj M) (Stacks.WeilCohomology.isInvertible_pullback_obj q M hM)
  have h₄ := e₁.symm.trans (h.symm.trans ((pullbackPicardHom_comp_apply α q _).trans
    ((congrArg (pullbackPicardHom α) e₂).trans e₃)))
  have hc := (h₁.trans (congrArg (hodgeFirstChernClassModule πP') h₄)).trans
    ((congrArg (hodgePullback α πP' πT γ wα 1 1) h₂).trans h₃).symm
  rw [hodgeAlgebraPullback_of, hodgeAlgebraPullback_of, hodgeAlgebraPullback_of]
  refine (congrArg (DirectSum.of (hodgePiece (formsAlgebras πP')) 2)
    (hodgePiecePullback_of ι πP' πP γ wι 2 bidegreeOneOne _)).trans ?_
  refine Eq.trans ?_ ((congrArg (fun z => DirectSum.of (hodgePiece (formsAlgebras πP')) 2
    (hodgePiecePullback α πP' πT γ wα 2 z))
    (hodgePiecePullback_of q πT πQ (𝟙 S) wq 2 bidegreeOneOne _)).trans
    (congrArg (DirectSum.of (hodgePiece (formsAlgebras πP')) 2)
      (hodgePiecePullback_of α πP' πT γ wα 2 bidegreeOneOne _))).symm
  exact congrArg (fun c : hodgeCohomologyComponent (formsAlgebras πP') 1 1 =>
    DirectSum.of (hodgePiece (formsAlgebras πP')) 2 (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
      (hodgeCohomologyComponent (formsAlgebras πP') i.1.1 (i.1.2 : ℤ) : Type u)) bidegreeOneOne c))
    hc

/-- **The projective bundle formula over an open on which the module is free**, granted the
formula for the trivial bundle `ℙʳ_k ×_k V ⟶ V` over affine `k`-schemes `V`: for `ℰ` free on `U`
and an affine open `V ⊆ U`, in every degree `k'` the map
`⨁_{i ≤ r} H^{k' - 2i}_{Hodge}(V/⊤) ⟶ H^{k'}_{Hodge}(p⁻¹V/⊤)`, `(a_i) ↦ ∑ ξ^i|_{p⁻¹V} ∪ p^*a_i`,
is bijective. The open `p⁻¹V` is `ℙʳ_k ×_k V` with `𝒪_P(1)` restricting to `𝒪(1)`
(`Stacks.HodgeWeil.exists_isPullback_bundleProj_restrict`), and the base `⊤ ⊆ Spec k` is
`Spec k`. -/
theorem bijective_hodgeLerayHirschSum_restrict_of_trivial
    (htriv : ∀ (V : Scheme.{u}) [IsAffine V] (t : V ⟶ Spec (.of k)) (r : ℕ) (n : ℤ),
      letI := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
      letI := hodgeAlgebraAlgebra
        (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      letI := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
      letI := hodgeGradedAlgebra
        (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      Function.Bijective (Stacks.WeilDeRham.degreewiseMap
        (hodgeGrade (formsAlgebras t) (hodgeScalarsOverField t))
        (hodgeGrade (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
          (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.snd (projToSpecCoeff k r) t)
          (specScalars k) t (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)
          (pullback.condition.symm.trans (Category.comp_id _).symm))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.fst (projToSpecCoeff k r) t)
          (specScalars k) (projToSpecCoeff k r)
          (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) (Category.comp_id _).symm 2
          _ (of_mem_hodgeGrade _ _ 2 (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
            (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) i.1.1 (i.1.2 : ℤ) :
              Type u)) bidegreeOneOne
            (hodgeFirstChernClassModule (projToSpecCoeff k r)
              (picardClassOf _ (projectiveTwistOne k r) (isInvertible_projectiveTwistOne k r))))))
        (r + 1) n))
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (U : X.Opens)
    (hU : Nonempty (E.restrict U.ι ≅
      SheafOfModules.free.{u} (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1)))))
    (V : X.Opens) (hVU : V ≤ U) (hV : IsAffineOpen V) (hVW : V ≤ s ⁻¹ᵁ ⊤) (n : ℤ) :
    Function.Bijective (hodgeLerayHirschSum (Stacks.Chow.bundleProj E ∣_ V) (s.resLE ⊤ V hVW)
      (Stacks.Chow.bundleProj E ∣_ V ≫ s.resLE ⊤ V hVW) (Category.comp_id _).symm
      (fun i : Fin (r + 1) => 2 * (i : ℕ))
      (fun i => hodgePiecePullback (Stacks.Chow.bundleProj E ⁻¹ᵁ V).ι
        (Stacks.Chow.bundleProj E ∣_ V ≫ s.resLE ⊤ V hVW) (Stacks.Chow.bundleProj E ≫ s)
        (⊤ : (Spec (.of k)).Opens).ι (restrict_w (Stacks.Chow.bundleProj E) s V ⊤ hVW) _
        ((hodgeBundleClass s E ^ (i : ℕ)) ((2 * (i : ℕ) : ℕ) : ℤ))) n) := by
  have : IsAffine V.toScheme := hV
  have : IsIso (⊤ : (Spec (.of k)).Opens).ι :=
    show IsIso (Scheme.topIso (Spec (.of k))).hom from inferInstance
  obtain ⟨pr₁, hsq, hpic⟩ : ∃ pr₁ : (Stacks.Chow.bundleProj E ⁻¹ᵁ V).toScheme ⟶
      Stacks.AlgebraicGeometry.ProjectiveSpaceHodge.projectiveSpace k r,
      IsPullback pr₁ (Stacks.Chow.bundleProj E ∣_ V) (projToSpecCoeff k r) (V.ι ≫ s) ∧
        pullbackPicardHom pr₁ (picardClassOf _ (projectiveTwistOne k r)
            (isInvertible_projectiveTwistOne k r)) =
          pullbackPicardHom (Stacks.Chow.bundleProj E ⁻¹ᵁ V).ι (picardClassOf _
            (Stacks.Chow.bundleTwist E) (Stacks.Chow.isInvertible_bundleTwist E)) :=
    exists_isPullback_bundleProj_restrict s E r U hU V hVU
  have hα : hsq.isoPullback.hom ≫ (pullback.fst (projToSpecCoeff k r) (V.ι ≫ s) ≫
      projToSpecCoeff k r) = (Stacks.Chow.bundleProj E ∣_ V ≫ s.resLE ⊤ V hVW) ≫
        (⊤ : (Spec (.of k)).Opens).ι := by
    rw [← Category.assoc, hsq.isoPullback_hom_fst, hsq.w, Category.assoc,
      restrictBase_w s V ⊤ hVW]
  have hβ : 𝟙 V.toScheme ≫ (V.ι ≫ s) = s.resLE ⊤ V hVW ≫ (⊤ : (Spec (.of k)).Opens).ι :=
    (Category.id_comp _).trans (restrictBase_w s V ⊤ hVW)
  have hp : Stacks.Chow.bundleProj E ∣_ V ≫ 𝟙 V.toScheme =
      hsq.isoPullback.hom ≫ pullback.snd (projToSpecCoeff k r) (V.ι ≫ s) :=
    (Category.comp_id _).trans hsq.isoPullback_hom_snd.symm
  have hξζ := (hodgeAlgebraPullback_hodgeFirstChernClass_eq (Stacks.Chow.bundleProj E ⁻¹ᵁ V).ι
    hsq.isoPullback.hom (pullback.fst (projToSpecCoeff k r) (V.ι ≫ s))
    (Stacks.Chow.bundleProj E ≫ s) (Stacks.Chow.bundleProj E ∣_ V ≫ s.resLE ⊤ V hVW)
    (pullback.fst (projToSpecCoeff k r) (V.ι ≫ s) ≫ projToSpecCoeff k r) (projToSpecCoeff k r)
    (⊤ : (Spec (.of k)).Opens).ι (restrict_w (Stacks.Chow.bundleProj E) s V ⊤ hVW) hα
    (Category.comp_id _).symm (Stacks.Chow.bundleTwist E) (Stacks.Chow.isInvertible_bundleTwist E)
    (projectiveTwistOne k r) (isInvertible_projectiveTwistOne k r)
    ((congrArg (fun φ => pullbackPicardHom φ (picardClassOf _ (projectiveTwistOne k r)
      (isInvertible_projectiveTwistOne k r))) hsq.isoPullback_hom_fst).trans hpic)).symm
  have hT := (bijective_degreewiseMap_iff (pullback.snd (projToSpecCoeff k r) (V.ι ≫ s)) (V.ι ≫ s)
    (pullback.fst (projToSpecCoeff k r) (V.ι ≫ s) ≫ projToSpecCoeff k r)
    (pullback.condition.symm.trans (Category.comp_id _).symm) (specScalars k) _ _ (r + 1) n).1
    (htriv V.toScheme (V.ι ≫ s) r n)
  exact bijective_hodgeLerayHirschSum_pow_of_isIso (pullback.snd _ _) (V.ι ≫ s)
    (pullback.fst _ _ ≫ projToSpecCoeff k r) _ (Stacks.Chow.bundleProj E ∣_ V) (s.resLE ⊤ V hVW)
    (Stacks.Chow.bundleProj E ∣_ V ≫ s.resLE ⊤ V hVW) (Category.comp_id _).symm
    hsq.isoPullback.hom (⊤ : (Spec (.of k)).Opens).ι hα hβ hp (Stacks.Chow.bundleProj E ⁻¹ᵁ V).ι
    (Stacks.Chow.bundleProj E ≫ s) (restrict_w (Stacks.Chow.bundleProj E) s V ⊤ hVW) _
    (hodgeBundleClass s E) hξζ (r + 1) n hT

/-- **The projective bundle formula for Hodge cohomology, from the formula for trivial
bundles**, for `𝐏(ℰ)` formed from any proof that `ℰ` is finite locally free: if for every affine
`k`-scheme `V` the formula holds for `ℙʳ_k ×_k V ⟶ V`, then for every `k`-scheme `X`, every
`ℰ` finite locally free of rank `r + 1` and every `n`, the map
`∏_{i ≤ r} H^{n - 2i}_{Hodge}(X/k) ⟶ H^n_{Hodge}(P/k)`, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)` with
`ξ = c₁^{Hodge}(𝒪_P(1))`, is bijective. -/
theorem bijective_degreewiseMap_hodgeBundleClass_of_trivial
    (htriv : ∀ (V : Scheme.{u}) [IsAffine V] (t : V ⟶ Spec (.of k)) (r : ℕ) (n : ℤ),
      letI := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
      letI := hodgeAlgebraAlgebra
        (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      letI := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
      letI := hodgeGradedAlgebra
        (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      Function.Bijective (Stacks.WeilDeRham.degreewiseMap
        (hodgeGrade (formsAlgebras t) (hodgeScalarsOverField t))
        (hodgeGrade (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
          (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.snd (projToSpecCoeff k r) t)
          (specScalars k) t (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)
          (pullback.condition.symm.trans (Category.comp_id _).symm))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.fst (projToSpecCoeff k r) t)
          (specScalars k) (projToSpecCoeff k r)
          (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) (Category.comp_id _).symm 2
          _ (of_mem_hodgeGrade _ _ 2 (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
            (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) i.1.1 (i.1.2 : ℤ) :
              Type u)) bidegreeOneOne
            (hodgeFirstChernClassModule (projToSpecCoeff k r)
              (picardClassOf _ (projectiveTwistOne k r) (isInvertible_projectiveTwistOne k r))))))
        (r + 1) n))
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (n : ℤ) :
    letI := hodgeAlgebraAlgebra (formsAlgebras s) (hodgeScalarsOverField s)
    letI := hodgeAlgebraAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
      (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s))
    letI := hodgeGradedAlgebra (formsAlgebras s) (hodgeScalarsOverField s)
    letI := hodgeGradedAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
      (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s))
    Function.Bijective (Stacks.WeilDeRham.degreewiseMap
      (hodgeGrade (formsAlgebras s) (hodgeScalarsOverField s))
      (hodgeGrade (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
        (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s)))
      (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (Stacks.Chow.bundleProj E) (specScalars k)
        s (Stacks.Chow.bundleProj E ≫ s) (Category.comp_id _).symm)
      (hodgeBundleClass_mem s E) (r + 1) n) := by
  refine (bijective_degreewiseMap_iff (Stacks.Chow.bundleProj E) s (Stacks.Chow.bundleProj E ≫ s)
    (Category.comp_id _).symm (specScalars k) (hodgeBundleClass s E) (hodgeBundleClass_mem s E)
    (r + 1) n).2 ?_
  let ξd : ∀ i : Fin (r + 1), dgaCohomology
      (hodgeDGA (Scheme.Hom.deRhamAlgebras (Stacks.Chow.bundleProj E ≫ s)))
      ((2 * (i : ℕ) : ℕ) : ℤ) := fun i =>
    (hodgeDgaEquiv (formsAlgebras (Stacks.Chow.bundleProj E ≫ s)) _).symm
      ((hodgeBundleClass s E ^ (i : ℕ)) ((2 * (i : ℕ) : ℕ) : ℤ))
  have hξd : (fun i : Fin (r + 1) => (hodgeBundleClass s E ^ (i : ℕ)) ((2 * (i : ℕ) : ℕ) : ℤ)) =
      fun i => hodgeDgaEquiv (formsAlgebras (Stacks.Chow.bundleProj E ≫ s)) _ (ξd i) :=
    funext fun i => ((hodgeDgaEquiv _ _).apply_symm_apply _).symm
  rw [hξd]
  refine (bijective_sum_dgaCohomologyCup_iff (Stacks.Chow.bundleProj E) s
    (fun i : Fin (r + 1) => 2 * (i : ℕ)) ξd n).1 ?_
  refine bijective_sum_dgaCohomologyCup_of_isBasis (Stacks.Chow.bundleProj E) s
    (fun i : Fin (r + 1) => 2 * (i : ℕ)) ξd (isBasis_affine_le_restrict_free E (r + 1))
    (fun V hV => ?_) n
  obtain ⟨hVaff, U, hVU, hU⟩ := hV
  have hVW : V ≤ s ⁻¹ᵁ ⊤ := fun x _ => trivial
  refine ⟨⊤, hVW, fun k' => ?_⟩
  refine (bijective_sum_dgaCohomologyCup_iff (Stacks.Chow.bundleProj E ∣_ V) (s.resLE ⊤ V hVW)
    _ _ k').2 ?_
  convert bijective_hodgeLerayHirschSum_restrict_of_trivial htriv s E r U hU V hVU hVaff hVW k'
    using 3 with i
  exact (hodgeDgaEquiv_pullback (Stacks.Chow.bundleProj E ⁻¹ᵁ V).ι
    (Stacks.Chow.bundleProj E ∣_ V ≫ s.resLE ⊤ V hVW) (Stacks.Chow.bundleProj E ≫ s)
    (⊤ : (Spec (.of k)).Opens).ι (restrict_w (Stacks.Chow.bundleProj E) s V ⊤ hVW) _
    (ξd i)).trans (congrArg _ ((hodgeDgaEquiv _ _).apply_symm_apply _))

/-- **The projective bundle formula for Hodge cohomology, from the formula for trivial
bundles over affine bases.** Let `k` be a field. Suppose that for every affine `k`-scheme
`t : V ⟶ Spec k`, every `r` and every `n`, the map
`∏_{i ≤ r} H^{n - 2i}_{Hodge}(V/k) ⟶ H^n_{Hodge}(ℙʳ_k ×_k V/k)`, `(a_i) ↦ ∑ ξ₀^i ∪ pr₂^*(a_i)`
with `ξ₀ = pr₁^*c₁^{Hodge}(𝒪(1))`, is bijective. Then for every `k`-scheme `s : X ⟶ Spec k`,
every finite locally free `𝒪_X`-module `ℰ` of rank `r + 1` with projective bundle
`p : P = 𝐏(ℰ) ⟶ X` and every `n`, the map
`∏_{i ≤ r} H^{n - 2i}_{Hodge}(X/k) ⟶ H^n_{Hodge}(P/k)`, `(a_i) ↦ ∑ ξ^i ∪ p^*(a_i)` with
`ξ = c₁^{Hodge}(𝒪_P(1))`, is bijective. -/
theorem bijective_degreewiseMap_bundle_of_trivial
    (htriv : ∀ (V : Scheme.{u}) [IsAffine V] (t : V ⟶ Spec (.of k)) (r : ℕ) (n : ℤ),
      letI := hodgeAlgebraAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
      letI := hodgeAlgebraAlgebra
        (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      letI := hodgeGradedAlgebra (formsAlgebras t) (hodgeScalarsOverField t)
      letI := hodgeGradedAlgebra
        (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
        (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
      Function.Bijective (Stacks.WeilDeRham.degreewiseMap
        (hodgeGrade (formsAlgebras t) (hodgeScalarsOverField t))
        (hodgeGrade (formsAlgebras (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r))
          (hodgeScalarsOverField (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.snd (projToSpecCoeff k r) t)
          (specScalars k) t (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r)
          (pullback.condition.symm.trans (Category.comp_id _).symm))
        (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (pullback.fst (projToSpecCoeff k r) t)
          (specScalars k) (projToSpecCoeff k r)
          (pullback.fst (projToSpecCoeff k r) t ≫ projToSpecCoeff k r) (Category.comp_id _).symm 2
          _ (of_mem_hodgeGrade _ _ 2 (DirectSum.of (fun i : HodgeBidegreeInt 2 =>
            (hodgeCohomologyComponent (formsAlgebras (projToSpecCoeff k r)) i.1.1 (i.1.2 : ℤ) :
              Type u)) bidegreeOneOne
            (hodgeFirstChernClassModule (projToSpecCoeff k r)
              (picardClassOf _ (projectiveTwistOne k r) (isInvertible_projectiveTwistOne k r))))))
        (r + 1) n))
    (X : Scheme.{u}) (s : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)] (n : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      E (r + 1)
    letI := hodgeAlgebraAlgebra (formsAlgebras s) (hodgeScalarsOverField s)
    letI := hodgeAlgebraAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
      (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s))
    letI := hodgeGradedAlgebra (formsAlgebras s) (hodgeScalarsOverField s)
    letI := hodgeGradedAlgebra (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
      (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s))
    Function.Bijective (Stacks.WeilDeRham.degreewiseMap
      (hodgeGrade (formsAlgebras s) (hodgeScalarsOverField s))
      (hodgeGrade (formsAlgebras (Stacks.Chow.bundleProj E ≫ s))
        (hodgeScalarsOverField (Stacks.Chow.bundleProj E ≫ s)))
      (hodgeAlgebraPullbackOverBase_mem_hodgeGrade (Stacks.Chow.bundleProj E) (specScalars k)
        s (Stacks.Chow.bundleProj E ≫ s) (Category.comp_id _).symm)
      (hodgeBundleClass_mem s E) (r + 1) n) := by
  have h := @bijective_degreewiseMap_hodgeBundleClass_of_trivial k _ htriv X s E r _
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)) n
  exact h

end Bundle

end Stacks.HodgeWeil

end
