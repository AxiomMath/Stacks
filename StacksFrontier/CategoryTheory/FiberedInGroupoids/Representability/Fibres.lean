module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Group.End

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# The fibre categories of `(𝒞/U) ×_𝒴 𝒳` over `𝒞/U`

Let `𝒞` be a category, let `𝒳`, `𝒴` be categories fibred in groupoids over `𝒞`, let `U` be an
object of `𝒞`, and let `F : 𝒳 ⥤ 𝒴` and `G : 𝒞/U ⥤ 𝒴` be 1-morphisms over `𝒞`. Stacks 02Y5
describes the fibre category of the 2-fibre product `(𝒞/U) ×_𝒴 𝒳` over an object `f : V ⟶ U`
of `𝒞/U`: its objects are the pairs `(x, φ)` with `x` an object of `𝒳_V` and `φ : G(f) ⟶ F(x)` a
morphism of `𝒴_V`, and a morphism `(x, φ) ⟶ (x', φ')` is a morphism `ψ : x ⟶ x'` of `𝒳_V` with
`F(ψ) = φ' ∘ φ⁻¹`.

## Main results

* `CategoryTheory.TwoFibreProductOver.FstFiber.objEquiv`, Stacks 02Y5 (1): the objects of the fibre
  over `f` are the pairs `(x, φ)`;
* `CategoryTheory.TwoFibreProductOver.FstFiber.homEquiv`, Stacks 02Y5 (2): the morphisms
  `(x, φ) ⟶ (x', φ')` of the fibre over `f` are the morphisms `ψ : x ⟶ x'` of `𝒳_V` with
  `F(ψ) = φ' ∘ φ⁻¹`;
* `CategoryTheory.TwoFibreProductOver.FstFiber.homEquiv_id` and
  `CategoryTheory.TwoFibreProductOver.FstFiber.homEquiv_comp`: the bijection on morphisms takes
  identities to identities and composition to composition.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver.FstFiber

open _root_.CategoryTheory.Functor

-- `Functor.Fiber` and `TwoFibreProductOver.fst` are plain `def`s, so a goal mentioning an object
-- of the fibre and its underlying object of the 2-fibre product is not type-correct at `implicit`
-- transparency.
attribute [local implicit_reducible] Functor.Fiber fst

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {U : 𝒞} {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴}
  {G : Over U ⥤ 𝒴} {f : Over U}

section

variable (A : (fst (Over.forget U) p𝒳 p𝒴 G F).Fiber f)

/-- The first component of an object of the fibre of `π₁` over `f` is `f` itself. -/
lemma x_eq : A.1.x = f := A.2

/-- The base object of an object of the fibre of `π₁` over `f` is the source `V` of `f`. -/
lemma base_eq : A.1.base = f.left := by
  rw [← A.1.hx, x_eq A]
  rfl

/-- The `𝒳`-component of an object of the fibre of `π₁` over `f` is an object of `𝒳_V`. -/
lemma obj_mem : p𝒳.obj A.1.y = f.left :=
  A.1.hy.trans (base_eq A)

/-- The comparison isomorphism `φ : G(f) ≅ F(x)` of an object of the fibre of `π₁` over `f`: the
comparison isomorphism of the underlying object of the 2-fibre product, whose source `G(P.x)` is
transported to `G(f)` along `P.x = f`. -/
def phiIso : G.obj f ≅ F.obj A.1.y :=
  eqToIso (congrArg G.obj (x_eq A).symm) ≪≫ A.1.iso

/-- The comparison isomorphism of an object of the fibre of `π₁` over `f` is a morphism of the
fibre `𝒴_V`, i.e. it lies over `id_V`. -/
lemma isHomLift_phiIso_hom : p𝒴.IsHomLift (𝟙 f.left) (phiIso A).hom := by
  have h := A.1.vertical
  rw [base_eq A] at h
  rw [phiIso, Iso.trans_hom, eqToIso.hom]
  infer_instance

end

/-- **Stacks 02Y5 (1).**
The objects of the fibre category of `(𝒞/U) ×_𝒴 𝒳` over an object `f : V ⟶ U` of `𝒞/U` are the
pairs `(x, φ)` consisting of an object `x` of the fibre `𝒳_V` and a morphism
`φ : G(f) ⟶ F(x)` of the fibre `𝒴_V`. -/
@[stacks 02Y5 "(1)"]
noncomputable def objEquiv (h𝒴 : p𝒴.IsFiberedInGroupoids) :
    (fst (Over.forget U) p𝒳 p𝒴 G F).Fiber f ≃
      Σ x : p𝒳.Fiber f.left, {φ : G.obj f ⟶ F.obj x.1 // p𝒴.IsHomLift (𝟙 f.left) φ} where
  toFun A := ⟨⟨A.1.y, obj_mem A⟩, ⟨(phiIso A).hom, isHomLift_phiIso_hom A⟩⟩
  invFun := fun ⟨⟨y, hy⟩, φ, hφ⟩ =>
    ⟨{ base := f.left
       x := f
       y := y
       hx := rfl
       hy := hy
       iso :=
        have := hφ
        have : IsIso φ :=
          have := h𝒴.isStronglyCartesian_homLift (𝟙 f.left) φ
          IsStronglyCartesian.isIso_of_base_isIso p𝒴 (𝟙 f.left) φ
        asIso φ
       vertical := hφ }, rfl⟩
  left_inv A := by
    obtain ⟨⟨base, x, y, hx, hy, iso, vertical⟩, hA⟩ := A
    obtain rfl : x = f := hA
    obtain rfl : (Over.forget U).obj x = base := hx
    apply Subtype.ext
    dsimp only [phiIso]
    congr 1
    exact Iso.ext (by simp)
  right_inv A := by
    obtain ⟨⟨x, hx⟩, ⟨φ, hφ⟩⟩ := A
    dsimp only [phiIso]
    ext <;> first | rfl | simp

section

variable {A B : (fst (Over.forget U) p𝒳 p𝒴 G F).Fiber f} (u : A ⟶ B)

/-- The `𝒞/U`-component of a morphism of the fibre of `π₁` over `f` is the identity of `f`,
transported along the equalities identifying the first components with `f`. -/
lemma hom_a_eq : u.1.a = eqToHom (x_eq A) ≫ eqToHom (x_eq B).symm := by
  have := u.2
  simpa using IsHomLift.fac' (fst (Over.forget U) p𝒳 p𝒴 G F) (𝟙 f) u.1

/-- The base component of a morphism of the fibre of `π₁` over `f` is the identity of `V`,
transported along the equalities identifying the base objects with `V`. -/
lemma hom_hbase_eq : u.1.hbase = eqToHom ((base_eq A).trans (base_eq B).symm) := by
  rw [Hom.hbase_eq, hom_a_eq]
  simp

/-- The `𝒳`-component of a morphism of the fibre of `π₁` over `f` is a morphism of the fibre
`𝒳_V`. -/
lemma isHomLift_hom_b : p𝒳.IsHomLift (𝟙 f.left) u.1.b := by
  have h := u.1.hb
  rw [hom_hbase_eq] at h
  exact IsHomLift.of_fac' p𝒳 _ _ (obj_mem A) (obj_mem B)
    (by rw [IsHomLift.fac' p𝒳 (eqToHom ((base_eq A).trans (base_eq B).symm)) u.1.b]; simp)

/-- The comparison square of a morphism of the fibre of `π₁` over `f`, in terms of the
comparison isomorphisms `φ` of its source and target: `F(ψ) = φ' ∘ φ⁻¹`. -/
lemma map_hom_b_eq : F.map u.1.b = (phiIso A).inv ≫ (phiIso B).hom := by
  have h := u.1.w
  rw [hom_a_eq] at h
  simp only [phiIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, eqToHom_map,
    Category.assoc, eqToHom_trans] at h ⊢
  rw [Iso.eq_inv_comp, ← h]
  simp

end

/-- **Stacks 02Y5 (2).**
The morphisms of the fibre category of `(𝒞/U) ×_𝒴 𝒳` over an object `f : V ⟶ U` of `𝒞/U` between
two objects `(x, φ)` and `(x', φ')` are exactly the morphisms `ψ : x ⟶ x'` of the fibre `𝒳_V`
with `F(ψ) = φ' ∘ φ⁻¹`. -/
@[stacks 02Y5 "(2)"]
def homEquiv (A B : (fst (Over.forget U) p𝒳 p𝒴 G F).Fiber f) :
    (A ⟶ B) ≃ {ψ : A.1.y ⟶ B.1.y // p𝒳.IsHomLift (𝟙 f.left) ψ ∧
      F.map ψ = (phiIso A).inv ≫ (phiIso B).hom} where
  toFun u := ⟨u.1.b, isHomLift_hom_b u, map_hom_b_eq u⟩
  invFun := fun ⟨ψ, hψ⟩ =>
    ⟨{ hbase := eqToHom ((base_eq A).trans (base_eq B).symm)
       a := eqToHom ((x_eq A).trans (x_eq B).symm)
       b := ψ
       ha := IsHomLift.of_fac' (Over.forget U) _ _ A.1.hx B.1.hx (by
        simp)
       hb :=
        have := hψ.1
        IsHomLift.of_fac' p𝒳 _ _ A.1.hy B.1.hy (by
          rw [IsHomLift.fac' p𝒳 (𝟙 f.left) ψ]
          simp [obj_mem])
       w := by
        have h := hψ.2
        simp only [phiIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
          Category.assoc] at h
        rw [eqToHom_map, h]
        simp },
      IsHomLift.of_fac' _ _ _ (x_eq A) (x_eq B) (by simp)⟩
  left_inv u := by
    refine Subtype.ext (Hom.ext' ?_ rfl)
    simp [hom_a_eq u]
  right_inv _ := rfl

/-- The bijection of Stacks 02Y5 (2) takes the identity to the identity. -/
lemma homEquiv_id (A : (fst (Over.forget U) p𝒳 p𝒴 G F).Fiber f) :
    (homEquiv A A (𝟙 A)).1 = 𝟙 A.1.y := rfl

/-- The bijection of Stacks 02Y5 (2) takes composition to composition. -/
lemma homEquiv_comp {A B C : (fst (Over.forget U) p𝒳 p𝒴 G F).Fiber f} (u : A ⟶ B)
    (v : B ⟶ C) :
    (homEquiv A C (u ≫ v)).1 = (homEquiv A B u).1 ≫ (homEquiv B C v).1 := rfl

end CategoryTheory.TwoFibreProductOver.FstFiber
