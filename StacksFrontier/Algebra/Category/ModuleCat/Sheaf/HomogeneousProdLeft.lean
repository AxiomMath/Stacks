module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# The left-handed ordered product of degree-one sections of a graded algebra

`Stacks.GradedAlgebra.homogeneousProd`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SymmetricPowerSheafification.lean`) multiplies
`n + 1` degree-one local sections by recursing on the **right**,
`z₀ ⋯ zₙ = (z₀ ⋯ zₙ₋₁) · zₙ`, because the resulting degree `(n : ℤ) + 1` is *definitionally*
`((n + 1 : ℕ) : ℤ)` and no transport is needed.

Stacks Tag 01CG, and every consumer that states a symmetric product as `s₀ · (s₁ ⋯ sₙ)`,
recurses on the **left** instead. That degree is `1 + (n : ℤ)`, which is only *propositionally*
`((n + 1 : ℕ) : ℤ)`, so the left-handed product has a transport baked into its definition and is
therefore a genuinely different term. This file introduces it and proves that the two agree.

## Main definitions

* `Stacks.GradedAlgebra.homogeneousProdLeft`: the ordered product of `n` degree-one local
  sections, multiplying on the left, with the degree transported along
  `1 + (n : ℤ) = ((n + 1 : ℕ) : ℤ)`.

## Main results

* `Stacks.GradedAlgebra.incl_homogeneousProdLeft`: the transport-free characterization — in the
  ungraded realization the left-handed product is the `List.prod` of the images of the factors,
  exactly as `Stacks.GradedAlgebra.incl_homogeneousProd` says of the right-handed one.
* `Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd`: **the two products agree.**
* `Stacks.GradedAlgebra.homogeneousProdLeft_naturality`: the left-handed product commutes with
  restriction.

## Implementation notes

* The transport is `Stacks.degCast`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleAbelian.lean`) rather than a
  hand-rolled `Eq.mp (congrArg ...)`: it is the transport the rest of the graded machinery uses,
  and `Stacks.degCast_rfl` makes `incl_degCast` hold by `subst`-then-`rfl`.
* The agreement is proved through `Stacks.GradedAlgebra.incl`, not by manipulating the
  transports: `incl` is injective (`Stacks.GradedAlgebra.incl_inj_of_proj` below, a two-line
  consequence of `Stacks.GradedAlgebra.proj_incl`), and both products become the same
  `List.prod` in the ungraded realization, where associativity is `DirectSum.GRing`'s and
  needs no `HEq`. This is why the `HEq` associativity of the graded multiplication is not used
  anywhere in this file.
* `incl_inj_of_proj` duplicates `Stacks.GradedAlgebra.incl_inj`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorAlgebraInhabitant.lean`) at a strictly
  greater generality: that version fixes the module universe to equal the ring universe
  (`Pz : ℤ → PresheafOfModules.{w}` over `O : Cᵒᵖ ⥤ CommRingCat.{w}`), whereas the graded
  algebras this file is about live in `PresheafOfModules.{max w a}`. The proof is the same
  `proj_incl` cancellation.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace Stacks.GradedAlgebra

section ProdLeft

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc)

/-- `Stacks.GradedAlgebra.incl` is injective, with `Stacks.GradedAlgebra.proj` as a left
inverse. -/
theorem incl_inj_of_proj {i : ℤ} {X : Cᵒᵖ} {x y : (Pc i).obj X} (h : A.incl i x = A.incl i y) :
    x = y := by
  have h2 := congrArg (A.proj X i) h
  rwa [A.proj_incl, A.proj_incl] at h2

/-- Transporting a homogeneous section along an equality of degrees does not change its image in
the ungraded realization. -/
theorem incl_degCast {X : Cᵒᵖ} {i j : ℤ} (h : i = j) (x : (Pc i).obj X) :
    A.incl j (_root_.Stacks.degCast (F := fun k : ℤ => ((Pc k).obj X : Type (max w a))) h x)
      = A.incl i x := by
  subst h
  rfl

/-- The ordered product of `n` degree-one local sections of a graded algebra, multiplying on the
left: `z₀ · (z₁ ⋯ zₙ₋₁)`. The empty product is the algebra unit.

Multiplying on the left produces degree `1 + (n : ℤ)`, which is only propositionally
`((n + 1 : ℕ) : ℤ)`, so a `Stacks.degCast` transport is part of the definition. The right-handed
`Stacks.GradedAlgebra.homogeneousProd` needs none; the two agree by
`Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd`. -/
noncomputable def homogeneousProdLeft (X : Cᵒᵖ) :
    (n : ℕ) → (Fin n → (Pc 1).obj X) → (Pc (n : ℤ)).obj X
  | 0, _ => A.one.eval X
  | n + 1, z =>
      _root_.Stacks.degCast (F := fun k : ℤ => ((Pc k).obj X : Type (max w a)))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)
        ((A.mul 1 (n : ℤ)).app X (z 0) (homogeneousProdLeft X n fun i => z i.succ))

/-- The left-handed ordered product of degree-one sections, read in the ungraded realization, is
the product of their images. This is the transport-free characterization of
`Stacks.GradedAlgebra.homogeneousProdLeft`, matching
`Stacks.GradedAlgebra.incl_homogeneousProd` for the right-handed product. -/
theorem incl_homogeneousProdLeft (X : Cᵒᵖ) (n : ℕ) (z : Fin n → (Pc 1).obj X) :
    A.incl (n : ℤ) (A.homogeneousProdLeft X n z) = (List.ofFn fun i => A.incl 1 (z i)).prod := by
  induction n with
  | zero =>
      rw [List.ofFn_zero, List.prod_nil]
      exact (A.one_eq_incl X).symm
  | succ n ih =>
      rw [homogeneousProdLeft,
        A.incl_degCast (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega),
        List.ofFn_succ, List.prod_cons, ← ih fun i => z i.succ]
      exact (A.incl_mul_incl 1 (n : ℤ) (z 0) (A.homogeneousProdLeft X n fun i => z i.succ)).symm

/-- **The left-handed and right-handed ordered products of degree-one sections agree.** Both have
the same image under the injective map `Stacks.GradedAlgebra.incl`, namely the `List.prod` of the
images of the factors. -/
theorem homogeneousProdLeft_eq_homogeneousProd (X : Cᵒᵖ) (n : ℕ) (z : Fin n → (Pc 1).obj X) :
    A.homogeneousProdLeft X n z = A.homogeneousProd X n z :=
  A.incl_inj_of_proj
    ((A.incl_homogeneousProdLeft X n z).trans (A.incl_homogeneousProd X n z).symm)

/-- The left-handed ordered product of degree-one sections commutes with restriction. -/
theorem homogeneousProdLeft_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℕ)
    (z : Fin n → (Pc 1).obj X) :
    (Pc (n : ℤ)).map f (A.homogeneousProdLeft X n z) =
      A.homogeneousProdLeft Y n fun i => (Pc 1).map f (z i) := by
  rw [A.homogeneousProdLeft_eq_homogeneousProd X n z,
    A.homogeneousProdLeft_eq_homogeneousProd Y n fun i => (Pc 1).map f (z i)]
  exact A.homogeneousProd_naturality f n z

end ProdLeft

end Stacks.GradedAlgebra
