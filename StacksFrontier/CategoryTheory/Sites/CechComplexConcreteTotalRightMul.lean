module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalCup

/-!
# The Čech cup product with a cochain of Čech degree zero is right multiplication

Let `D` be a pairing `K^a ⊗ L^b ⟶ M^{a+b}` of `ℤ`-indexed complexes of presheaves of
`R`-modules on a category with finite products, and let `P`, `Q`, `T` be `ℕ`-indexed complexes
identified with `K`, `L`, `M` in nonnegative degrees, through which `D` becomes a family `μc` of
biadditive maps. For `x ∈ Tot^m(Č(W, P))` and a Čech `0`-cochain `y` of `Q^b`, the
Alexander--Whitney cup product of the library (`Stacks.Cech.LinearCupProduct.cechCupProduct`) of
`x` with `y`, read on the elementwise total complexes through
`Stacks.CategoryTheory.CechComplex.totalCechIso`, is the right multiplication
`Stacks.CategoryTheory.CechComplex.rightMul` of `x` by `y`:

`(x ∪ y)_t = μ(x_t, y_{t_r}|_{U_t})` on the summand of Čech degree `r`.

## Main results

* `Stacks.CategoryTheory.CechComplex.totalTo_cechCupProduct_totalFrom`: the formula above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open Stacks.Cech.LinearCupProduct (PresheafModules cechCochains cechCochainsMap
  totalCechComplexFunctor ιTotalCechTo ComplexPairing cechCupProduct ιTensorSource ιTensorSource_eq)
open Stacks.Cech.Hypercohomology (toMor unitModule)

universe u uC vC

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize totIndexFintype

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] {ι : Type u} (W : ι → C)
  {R : Type u} [CommRing R] {P Q T : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (μc : ∀ (a b c : ℕ), a + b = c → ∀ V : Cᵒᵖ,
    (P.X a).obj V →+ (Q.X b).obj V →+ (T.X c).obj V)
  {K L M : CochainComplex (PresheafModules.{u} C R) ℤ}
  (eK : ∀ b : ℕ, K.X (b : ℤ) ≅ P.X b) (eL : ∀ b : ℕ, L.X (b : ℤ) ≅ Q.X b)
  (eM : ∀ b : ℕ, M.X (b : ℤ) ≅ T.X b) (D : ComplexPairing R K L M)

/-- The pure tensor `a ⊗ b` in the tensor product of two modules, as an element of the value of
the tensor bifunctor. -/
def tmulHom {A B : ModuleCat.{u} R} (a : A) (b : B) :
    ((Stacks.Cech.CupProduct.tensorModules.{u, u} R).obj A).obj B :=
  a ⊗ₜ[R] b

variable (K L) in
/-- The inclusion of the bidegree `(m, b)` into the degree-`N` term of the tensor product of two
total Čech complexes. -/
def ιTot (m b N : ℤ) (hN : m + b = N) :
    ((Stacks.Cech.CupProduct.tensorModules.{u, u} R).obj
        (((totalCechComplexFunctor W R).obj K).X m)).obj
        (((totalCechComplexFunctor W R).obj L).X b) ⟶
      (HomologicalComplex.mapBifunctor ((totalCechComplexFunctor W R).obj K)
        ((totalCechComplexFunctor W R).obj L) (Stacks.Cech.CupProduct.tensorModules.{u, u} R)
          (ComplexShape.up ℤ)).X N :=
  HomologicalComplex.ιMapBifunctor _ _ _ _ m b N hN

/-- `tmulHom` is additive in its first argument over a finite sum. -/
theorem tmulHom_sum_left {A B : ModuleCat.{u} R} {J : Type*} (s : Finset J) (a : J → A) (b : B) :
    tmulHom (∑ j ∈ s, a j) b = ∑ j ∈ s, tmulHom (a j) b :=
  TensorProduct.sum_tmul s a b

/-- On the image of a Čech `r`-cochain of `K^a` and a Čech `0`-cochain of `L^b` in the total
complexes, the cup product precomposed with `ιTot` is the cup product precomposed with the
inclusion `ιTensorSource` of the summand of bidegrees `(r, a)` and `(0, b)`. -/
theorem ιTot_ιTotalCechTo (r a b : ℕ) (m N : ℤ) (hm : (r : ℤ) + a = m) (hN : m + b = N)
    (c : cechCochains W R (K.X a) r) (d : cechCochains W R (L.X b) 0) :
    (ιTot W K L m b N hN ≫ (cechCupProduct W R D).f N).hom
        (tmulHom ((ιTotalCechTo W R K r a m hm).hom c)
          ((ιTotalCechTo W R L 0 b b (by simp)).hom d)) =
      (ιTensorSource W R K L r 0 a b N (by push_cast; omega) ≫ (cechCupProduct W R D).f N).hom
        (c ⊗ₜ[R] d) := by
  rw [← ιTensorSource_eq W R K L r 0 a b m b N hm (by simp) hN]
  rfl

variable (hμ : ∀ (a b : ℕ) (V : Cᵒᵖ) (x : (K.X a).obj V) (y : (L.X b).obj V),
      ((eM (a + b)).hom.app V).hom (((D.μ a b (a + b) rfl).app V).hom (x ⊗ₜ y)) =
        μc a b (a + b) rfl V (((eK a).hom.app V).hom x) (((eL b).hom.app V).hom y))

include hμ in
/-- The cup product of a single summand `totSingle W P m r a hm c` of `Tot^m(Č(W, P))` with the
Čech `0`-cochain `y` of coefficient degree `b`, read on the elementwise total complexes, is the
right multiplication of that summand by `y`. -/
theorem totalTo_cechCupProduct_totSingle (b r a : ℕ) {m N : ℤ} (hm : (r : ℤ) + a = m)
    (hN : m + b = N) (c : Cochain W (P.X a) r) (y : Cochain W (Q.X b) 0) :
    (totalTo W M T eM N).hom ((ιTot W K L m b N hN ≫ (cechCupProduct W R D).f N).hom
        (tmulHom ((totalFrom W K P eK m).hom (totSingle W P m r a hm c))
          ((totalFrom W L Q eL b).hom (totSingle W Q b 0 b (by simp) y)))) =
      rightMul W μc b y hN (totSingle W P m r a hm c) := by
  subst hm
  rw [totalFrom_totSingle, totalFrom_totSingle, ιTot_ιTotalCechTo]
  exact totalTo_ιTensorSource_cechCupProduct_zero W μc eK D eL eM hμ r a b N _ c y

include hμ in
/-- **The cup product with a cochain of Čech degree `0`, on the elementwise total complexes**:
when the coefficient pairing `D` is `μc` through the identifications `eK`, `eL`, `eM`, the cup
product of `x ∈ Tot^m(Č(W, P))` with the Čech `0`-cochain `y` of coefficient degree `b` is the
right multiplication of `x` by `y`. -/
theorem totalTo_cechCupProduct_totalFrom (b : ℕ) {m N : ℤ} (hN : m + b = N) (x : TotX W P m)
    (y : Cochain W (Q.X b) 0) :
    (totalTo W M T eM N).hom ((ιTot W K L m b N hN ≫ (cechCupProduct W R D).f N).hom
        (tmulHom ((totalFrom W K P eK m).hom x)
          ((totalFrom W L Q eL b).hom (totSingle W Q b 0 b (by simp) y)))) =
      rightMul W μc b y hN x := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single x]
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, tmulHom_sum_left, map_sum, map_sum, rightMul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact totalTo_cechCupProduct_totSingle W μc eK eL eM D hμ b i.1.1 i.1.2 i.2 hN (x i) y

include hμ in
/-- When `M` vanishes in negative degrees, the image under `totalFrom` of the right
multiplication of `x ∈ Tot^m(Č(W, P))` by the Čech `0`-cochain `y` is the cup product of the images
of `x` and `y` in the library's total complexes. -/
theorem totalFrom_rightMul (hz : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (b : ℕ) {m N : ℤ}
    (hN : m + b = N) (x : TotX W P m) (y : Cochain W (Q.X b) 0) :
    (totalFrom W M T eM N).hom (rightMul W μc b y hN x) =
      (ιTot W K L m b N hN ≫ (cechCupProduct W R D).f N).hom
        (tmulHom ((totalFrom W K P eK m).hom x)
          ((totalFrom W L Q eL b).hom (totSingle W Q b 0 b (by simp) y))) := by
  rw [← totalTo_cechCupProduct_totalFrom W μc eK eL eM D hμ b hN x y]
  exact totalFrom_totalTo_apply W M T eM hz N _

end

end Stacks.CategoryTheory.CechComplex
