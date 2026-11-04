module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Integral closure commutes with smooth base change

Let `R → S` be a smooth ring map, let `R → B` be an arbitrary ring map, let
`A = integralClosure R B` and let `A' = integralClosure S (S ⊗[R] B)`. The canonical `S`-algebra
map `S ⊗[R] A → A'`, `s ⊗ a ↦ s ⊗ a`, is an isomorphism.

## Main results

* `Stacks.IntegralClosure.SmoothBaseChange.solution`: for `S` smooth over `R` and `B` an arbitrary
  `R`-algebra, the canonical map `S ⊗[R] integralClosure R B → integralClosure S (S ⊗[R] B)` is
  bijective.

## References

* [Stacks 03GG](https://stacks.math.columbia.edu/tag/03GG)
-/

@[expose] public section

namespace Stacks.IntegralClosure.SmoothBaseChange

/-- For `S` smooth over `R` and `B` an arbitrary `R`-algebra, the canonical map
`S ⊗[R] integralClosure R B → integralClosure S (S ⊗[R] B)` is bijective. -/
public theorem solution {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective (TensorProduct.toIntegralClosure R S B) :=
  TensorProduct.toIntegralClosure_bijective_of_smooth

end Stacks.IntegralClosure.SmoothBaseChange

end

/-!
# Integral closure commutes with smooth base change

Let `R → S` be a smooth ring map and `R → B` an arbitrary ring map, let `A = integralClosure R B`
be the integral closure of `R` in `B`, and let `A' = integralClosure S (S ⊗[R] B)` be the integral
closure of `S` in `S ⊗[R] B`. An element of `A` stays integral over `S` after base change, so there
is a canonical `S`-algebra map
```
S ⊗[R] A → A' ,   s ⊗ a ↦ s ⊗ a ,
```
namely `TensorProduct.toIntegralClosure R S B`. This map is an isomorphism.

## Main results

* `Algebra.Smooth.toIntegralClosure_bijective`: for `S` smooth over `R`, the canonical map
  `S ⊗[R] integralClosure R B → integralClosure S (S ⊗[R] B)` is bijective.

## References

* [StacksProject 03GG](https://stacks.math.columbia.edu/tag/03GG)
* [StacksProject 03GE](https://stacks.math.columbia.edu/tag/03GE)
* [StacksProject 00TA](https://stacks.math.columbia.edu/tag/00TA)

## Tags

integral closure, base change, smooth ring map, tensor product
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.Smooth

/-- Let `R → S` be a smooth ring map, let `R → B` be any ring map, let
`A = integralClosure R B` be the integral closure of `R` in `B` and let
`A' = integralClosure S (S ⊗[R] B)` be the integral closure of `S` in `S ⊗[R] B`. Then the
canonical map `S ⊗[R] A → A'`, `s ⊗ a ↦ s ⊗ a`, is an isomorphism. -/
@[stacks 03GG "The isomorphism of the tag is bijectivity of Mathlib's canonical map
`TensorProduct.toIntegralClosure`, whose `AlgEquiv` form is `AlgEquiv.ofBijective` applied to it.
This is Mathlib's `TensorProduct.toIntegralClosure_bijective_of_smooth`, which carries no
`@[stacks]` tag upstream. See the module docstring.",
  ega "IV 18.12.15" "more general",
  ega "IV 6.14.5" "smooth base change"]
public theorem toIntegralClosure_bijective {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective (TensorProduct.toIntegralClosure R S B) :=
  Stacks.IntegralClosure.SmoothBaseChange.solution

end Algebra.Smooth

end

/-!
# Integral closure and base change along a filtered colimit of algebras

Let `R → S` and `R → B` be ring maps, let `A = integralClosure R B` and let
`A' = integralClosure S (S ⊗[R] B)`. If `S` is the colimit of a directed system of `R`-algebras
`G i` for which the canonical map `G i ⊗[R] A → integralClosure (G i) (G i ⊗[R] B)` is bijective,
then `S ⊗[R] A → A'` is bijective.

## Main results

* `Stacks.IntegralClosure.ColimitBaseChange.solution`: if `S` is the colimit of a directed system
  of `R`-algebras `G i` for which `G i ⊗[R] A → integralClosure (G i) (G i ⊗[R] B)` is bijective,
  then `S ⊗[R] A → A'` is bijective.

## References

* [StacksProject 0CBF](https://stacks.math.columbia.edu/tag/0CBF)
* [StacksProject 03GG](https://stacks.math.columbia.edu/tag/03GG)
-/

namespace Stacks.IntegralClosure.ColimitBaseChange

open scoped TensorProduct
open Algebra.TensorProduct

section Functoriality
variable {R C D E M N B : Type*} [CommRing R] [CommRing C] [CommRing D] [CommRing E] [CommRing M]
  [CommRing N] [CommRing B] [Algebra R C] [Algebra R D] [Algebra R E] [Algebra R M] [Algebra R N]
  [Algebra R B]

private theorem rTensor_rTensor (φ : C →ₐ[R] D) (χ : D →ₐ[R] E) (x : C ⊗[R] M) :
    rTensor M χ (rTensor M φ x) = rTensor M (χ.comp φ) x := by
  rw [← AlgHom.comp_apply, ← map_comp]; simp

private theorem lTensor_rTensor (φ : C →ₐ[R] D) (ψ : M →ₐ[R] N) (x : C ⊗[R] M) :
    lTensor (S := R) D ψ (rTensor M φ x) = rTensor N φ (lTensor (S := R) C ψ x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← map_comp, ← map_comp]; simp

/-- `TensorProduct.toIntegralClosure` is natural in the left tensor factor. -/
private theorem coe_toIntegralClosure_rTensor (φ : C →ₐ[R] D) (w : C ⊗[R] integralClosure R B) :
    (TensorProduct.toIntegralClosure R D B (rTensor (integralClosure R B) φ w) : D ⊗[R] B) =
      rTensor B φ (TensorProduct.toIntegralClosure R C B w) :=
  lTensor_rTensor φ (integralClosure R B).val w

/-- Evaluating a polynomial commutes with base change of its coefficients. -/
private theorem rTensor_aeval (φ : C →ₐ[R] D) (y : C ⊗[R] B) (q : Polynomial C) :
    rTensor B φ (Polynomial.aeval y q) =
      Polynomial.aeval (rTensor B φ y) (q.map (φ : C →+* D)) :=
  Polynomial.map_aeval_eq_aeval_map (by ext c; simp) q y

end Functoriality

section Colimit
variable {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {G : ι → Type*} [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
  (F : ∀ i j, i ≤ j → (G i →ₐ[R] G j)) [DirectedSystem G fun i j h ↦ F i j h]
  {S : Type*} [CommRing S] [Algebra R S]

omit [IsDirectedOrder ι] [Nonempty ι] in
private theorem directedSystem_rTensor (M : Type*) [CommRing M] [Algebra R M] :
    DirectedSystem (fun i ↦ G i ⊗[R] M)
      fun i j h ↦ (rTensor M (F i j h) : G i ⊗[R] M → G j ⊗[R] M) where
  map_self i x := by
    rw [show F i i le_rfl = AlgHom.id R (G i) from AlgHom.ext fun y ↦ DirectedSystem.map_self' F y]
    simp
  map_map _ _ _ hij hjk x := by
    rw [rTensor_rTensor, show (F _ _ hjk).comp (F _ _ hij) = F _ _ (hij.trans hjk) from
      AlgHom.ext (DirectedSystem.map_map' F hij hjk)]

attribute [local instance] directedSystem_rTensor

/-- The map from the stage `G i` to `S`, through a presentation `e` of `S` as the colimit. -/
private noncomputable def stageHom (e : DirectLimit G F ≃ₐ[R] S) (i : ι) : G i →ₐ[R] S :=
  e.toAlgHom.comp (DirectLimit.Algebra.of G F i)

private theorem stageHom_comp (e : DirectLimit G F ≃ₐ[R] S) {i j : ι} (h : i ≤ j) :
    (stageHom F e j).comp (F i j h) = stageHom F e i := by
  ext x
  simp [stageHom]

/-- Mapping `G i ⊗[R] M` to a later stage and then to `S ⊗[R] M` agrees with mapping directly. -/
private theorem rTensor_stageHom_rTensor (e : DirectLimit G F ≃ₐ[R] S) (M : Type*) [CommRing M]
    [Algebra R M] {i j : ι} (h : i ≤ j) (x : G i ⊗[R] M) :
    rTensor M (stageHom F e j) (rTensor M (F i j h) x) = rTensor M (stageHom F e i) x := by
  rw [rTensor_rTensor, stageHom_comp]

private theorem exists_stageHom_eq (e : DirectLimit G F ≃ₐ[R] S) (s : S) :
    ∃ (i : ι) (x : G i), stageHom F e i x = s := by
  obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk F (e.symm s)
  exact ⟨i, x, by simp [stageHom, ← hx]⟩

/-- Tensoring with `M` commutes with the colimit of a directed system of `R`-algebras:
`colim_i (G i ⊗[R] M) ≃ S ⊗[R] M`, sending the class of `x : G i ⊗[R] M` to its image under the
stagewise map `G i →ₐ[R] S`. -/
private noncomputable def stageTensorEquiv (e : DirectLimit G F ≃ₐ[R] S) (M : Type*) [CommRing M]
    [Algebra R M] :
    DirectLimit (fun i ↦ G i ⊗[R] M) (fun i j h ↦ rTensor M (F i j h)) ≃ₗ[R] S ⊗[R] M :=
  LinearEquiv.ofLinearMap
    (DirectLimit.Algebra.lift _ _ _ (fun i ↦ rTensor M (stageHom F e i)) 
      fun _ _ h ↦ rTensor_stageHom_rTensor F e M h).toLinearMap
    (TensorProduct.lift (DirectLimit.Module.lift R ι G F
      (fun i ↦ (TensorProduct.mk R (G i) M).compr₂
        (DirectLimit.Module.of R ι (fun i ↦ G i ⊗[R] M) (fun i j h ↦ rTensor M (F i j h)) i))
      (fun i j h x ↦ by
        ext m
        exact DirectLimit.Module.of_f (G := fun i ↦ G i ⊗[R] M)
          (f := fun i j h ↦ rTensor M (F i j h)) (x := x ⊗ₜ m))
      ∘ₗ e.symm.toLinearEquiv.toLinearMap))
    (by
      ext s m
      obtain ⟨i, x, rfl⟩ := exists_stageHom_eq F e s
      simp [stageHom])
    (by ext i x m; simp [stageHom])

private theorem stageTensorEquiv_mk (e : DirectLimit G F ≃ₐ[R] S) (M : Type*) [CommRing M]
    [Algebra R M] (i : ι) (x : G i ⊗[R] M) :
    stageTensorEquiv F e M ⟦⟨i, x⟩⟧ = rTensor M (stageHom F e i) x := rfl

/-- Every element of `S ⊗[R] M` comes from some stage of the system. -/
private theorem exists_rTensor_eq (e : DirectLimit G F ≃ₐ[R] S) (M : Type*) [CommRing M]
    [Algebra R M] (z : S ⊗[R] M) :
    ∃ (i : ι) (x : G i ⊗[R] M), rTensor M (stageHom F e i) x = z := by
  obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk _ ((stageTensorEquiv F e M).symm z)
  exact ⟨i, x, by rw [← stageTensorEquiv_mk, ← hx, LinearEquiv.apply_symm_apply]⟩

/-- An element of a stage that dies in `S ⊗[R] M` already dies at a later stage. -/
private theorem exists_rTensor_eq_zero (e : DirectLimit G F ≃ₐ[R] S) (M : Type*) [CommRing M]
    [Algebra R M] {i : ι} {x : G i ⊗[R] M} (hx : rTensor M (stageHom F e i) x = 0) :
    ∃ (j : ι) (h : i ≤ j), rTensor M (F i j h) x = 0 := by
  have h0 : (⟦⟨i, x⟩⟧ : DirectLimit (fun i ↦ G i ⊗[R] M) fun i j h ↦ rTensor M (F i j h))
      = ⟦⟨i, 0⟩⟧ := by
    apply (stageTensorEquiv F e M).injective
    rw [stageTensorEquiv_mk, stageTensorEquiv_mk, hx, map_zero]
  obtain ⟨j, hij, _, hj⟩ := Quotient.exact h0
  exact ⟨j, hij, by simpa using hj⟩

/-- Taking integral closures commutes with the colimit: an element of `S ⊗[R] B` integral over `S`
is the image of an element of some `G k ⊗[R] B` integral over `G k`. -/
private theorem exists_isIntegral_rTensor_eq (e : DirectLimit G F ≃ₐ[R] S) (B : Type*) [CommRing B]
    [Algebra R B] {z : S ⊗[R] B} (hz : IsIntegral S z) :
    ∃ (k : ι) (y : G k ⊗[R] B), IsIntegral (G k) y ∧ rTensor B (stageHom F e k) y = z := by
  classical
  obtain ⟨p, hpm, hp⟩ := hz
  obtain ⟨i, x, hx⟩ := exists_rTensor_eq F e B z
  choose ic xc hxc using fun n : ℕ ↦ exists_stageHom_eq F e (p.coeff n)
  obtain ⟨j, hjle⟩ := Finset.exists_le (insert i (p.support.image ic))
  have hij : i ≤ j := hjle i (Finset.mem_insert_self _ _)
  obtain ⟨y, hyz⟩ : ∃ y : G j ⊗[R] B, rTensor B (stageHom F e j) y = z :=
    ⟨rTensor B (F i j hij) x, by rw [rTensor_stageHom_rTensor, hx]⟩
  have hlift : p ∈ Polynomial.lifts (stageHom F e j : G j →+* S) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n ↦ ?_
    by_cases hn : n ∈ p.support
    · have hle : ic n ≤ j := hjle _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn))
      exact ⟨F (ic n) j hle (xc n), by rw [← hxc n, ← stageHom_comp F e hle]; rfl⟩
    · exact ⟨0, by rw [map_zero, Polynomial.notMem_support_iff.mp hn]⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hpm
  obtain ⟨k, hjk, hk⟩ := exists_rTensor_eq_zero F e B
    (show rTensor B (stageHom F e j) (Polynomial.aeval y q) = 0 by
      rw [rTensor_aeval, hq, hyz, Polynomial.aeval_def]; exact hp)
  refine ⟨k, rTensor B (F j k hjk) y, ⟨q.map (F j k hjk : G j →+* G k), hqm.map _, ?_⟩, ?_⟩
  · rw [← Polynomial.aeval_def, ← rTensor_aeval]; exact hk
  · rw [rTensor_stageHom_rTensor, hyz]

end Colimit

/-- Let `R → S` and `R → B` be ring maps, let `A = integralClosure R B` and let
`A' = integralClosure S (S ⊗[R] B)`. If `S` is `R`-algebra
isomorphic to the colimit of a directed system `G` of `R`-algebras for which the canonical map
`G i ⊗[R] A → integralClosure (G i) (G i ⊗[R] B)` is bijective at every stage, then the canonical
map `S ⊗[R] A → A'` is bijective. -/
public theorem solution {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type*} [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
    (F : ∀ i j, i ≤ j → (G i →ₐ[R] G j)) [DirectedSystem G fun i j h ↦ F i j h]
    (e : DirectLimit G F ≃ₐ[R] S)
    (H : ∀ i, Function.Bijective (TensorProduct.toIntegralClosure R (G i) B)) :
    Function.Bijective (TensorProduct.toIntegralClosure R S B) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun w hw ↦ ?_, ?_⟩
  · obtain ⟨i, v, rfl⟩ := exists_rTensor_eq F e (integralClosure R B) w
    obtain ⟨j, hij, hj⟩ := exists_rTensor_eq_zero F e B (i := i)
      (x := (TensorProduct.toIntegralClosure R (G i) B v : G i ⊗[R] B))
      (by rw [← coe_toIntegralClosure_rTensor, hw, ZeroMemClass.coe_zero])
    have h : rTensor (integralClosure R B) (F i j hij) v = 0 :=
      (injective_iff_map_eq_zero _).mp (H j).injective _
        (Subtype.ext (by rw [coe_toIntegralClosure_rTensor, hj, ZeroMemClass.coe_zero]))
    rw [← rTensor_stageHom_rTensor F e _ hij, h, map_zero]
  · rintro ⟨z, hz⟩
    obtain ⟨k, y, hy, hyz⟩ := exists_isIntegral_rTensor_eq F e B hz
    obtain ⟨v, hv⟩ := (H k).surjective ⟨y, hy⟩
    exact ⟨rTensor (integralClosure R B) (stageHom F e k) v,
      Subtype.ext (by rw [coe_toIntegralClosure_rTensor, hv]; exact hyz)⟩

end Stacks.IntegralClosure.ColimitBaseChange

/-!
# Integral closure and base change along a filtered colimit of algebras

Let `R → S` and `R → B` be ring maps, let `A = integralClosure R B` be the integral closure of
`R` in `B`, and let `A' = integralClosure S (S ⊗[R] B)` be the integral closure of `S` in
`S ⊗[R] B`. Every element of `A` stays integral after base change, so there is a canonical
`S`-algebra map
```
S ⊗[R] A → A' ,   s ⊗ a ↦ s ⊗ a ,
```
namely `TensorProduct.toIntegralClosure R S B`. This map is an isomorphism as soon as `S` is a
filtered colimit of smooth `R`-algebras.

## Main results

* `TensorProduct.toIntegralClosure_bijective_of_directLimit`: if `S` is the colimit of a directed
  system of `R`-algebras `G i` for which
  `G i ⊗[R] integralClosure R B → integralClosure (G i) (G i ⊗[R] B)` is bijective, then
  `S ⊗[R] integralClosure R B → integralClosure S (S ⊗[R] B)` is bijective.
* `TensorProduct.toIntegralClosure_bijective_of_directLimit_smooth`: the case of a directed system
  of smooth `R`-algebras.

## References

* [StacksProject 0CBF](https://stacks.math.columbia.edu/tag/0CBF)
* [StacksProject 03GG](https://stacks.math.columbia.edu/tag/03GG)
* [StacksProject 07C3](https://stacks.math.columbia.edu/tag/07C3)

## Tags

integral closure, base change, smooth ring map, filtered colimit, direct limit
-/

@[expose] public section

open scoped TensorProduct

/-- Let `R → S` and `R → B` be ring maps, let `A = integralClosure R B` and let
`A' = integralClosure S (S ⊗[R] B)`. If `S` is `R`-algebra isomorphic to the colimit
`DirectLimit G F` of a directed system `G` of `R`-algebras and the canonical map
`G i ⊗[R] A → integralClosure (G i) (G i ⊗[R] B)` is bijective for every `i`, then the canonical
map `S ⊗[R] A → A'` is bijective. -/
@[stacks 0CBF "The colimit step of the tag, with the smoothness of the stages weakened to what
the argument uses: bijectivity of the map at each stage. The tag's own hypothesis is recovered in
`TensorProduct.toIntegralClosure_bijective_of_directLimit_smooth` below. The filtered colimit is
spelled as a colimit over a directed nonempty preorder, presented by an `R`-algebra equivalence
`DirectLimit G F ≃ₐ[R] S` so that the conclusion is about an abstract `S`; the isomorphism of the
tag is bijectivity of Mathlib's canonical map `TensorProduct.toIntegralClosure`, as in the smooth
case 03GG. See the module docstring."]
public theorem TensorProduct.toIntegralClosure_bijective_of_directLimit
    {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type*} [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
    (F : ∀ i j, i ≤ j → (G i →ₐ[R] G j)) [DirectedSystem G fun i j h ↦ F i j h]
    (e : DirectLimit G F ≃ₐ[R] S)
    (H : ∀ i, Function.Bijective (TensorProduct.toIntegralClosure R (G i) B)) :
    Function.Bijective (TensorProduct.toIntegralClosure R S B) :=
  Stacks.IntegralClosure.ColimitBaseChange.solution F e H

/-- Let `R → S` and `R → B` be ring maps, let `A = integralClosure R B` and let
`A' = integralClosure S (S ⊗[R] B)`. If `S` is `R`-algebra isomorphic to the colimit
`DirectLimit G F` of a directed system `G` of smooth `R`-algebras, then the canonical map
`S ⊗[R] A → A'` is an isomorphism. -/
@[stacks 0CBF "The literal form of the tag, as the colimit step
`TensorProduct.toIntegralClosure_bijective_of_directLimit` applied to the smooth case 03GG
(`TensorProduct.toIntegralClosure_bijective_of_smooth`).",
  ega "IV 6.14.5" "colimit of smooth base",
  ega "IV 18.12.15"]
public theorem TensorProduct.toIntegralClosure_bijective_of_directLimit_smooth
    {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {G : ι → Type*} [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)] [∀ i, Algebra.Smooth R (G i)]
    (F : ∀ i j, i ≤ j → (G i →ₐ[R] G j)) [DirectedSystem G fun i j h ↦ F i j h]
    (e : DirectLimit G F ≃ₐ[R] S) :
    Function.Bijective (TensorProduct.toIntegralClosure R S B) :=
  toIntegralClosure_bijective_of_directLimit F e fun _ ↦
    TensorProduct.toIntegralClosure_bijective_of_smooth

end
