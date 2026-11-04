module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.Algebra.Homology.DerivedCategory.UniformUpperBounds
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# Derived tensor products along a tower of short exact sequences of sheaves of modules

Let `(C, O)` be a ringed site, `T` a derived tensor product on `D(O)` and `K` an object of
`D(O)`. A short exact sequence `0 → F₁ → F₂ → F₃ → 0` of sheaves of `O`-modules gives a
distinguished triangle in `D(O)`, and `K ⊗^L_O -` is exact, so the derived tensor products of
`K` with the three terms sit in a distinguished triangle. A tower of such sequences whose
quotients are the successive terms of a family of `O`-modules therefore propagates an upper
cohomological bound from the first term and the subobjects to the whole family, uniformly.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.mapTriangle_singleTriangle_distinguished`: the
  derived tensor product of `K` with a short exact sequence of `O`-modules is a distinguished
  triangle.
* `Stacks.SheafOfModules.DerivedTensorProduct.isUniformlyBoundedAbove_tensor_of_tower`: a tower
  of short exact sequences with uniformly bounded above subobjects gives a uniform upper bound
  on the whole tower.
* `Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_X₂`: vanishing of
  the cohomology in one degree after tensoring with `K` passes from the outer terms of a short
  exact sequence of `O`-modules to the middle one.
* `Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_of_tower`: along an
  increasing tower of short exact sequences whose quotients and whose first term all have
  vanishing cohomology in one degree after tensoring with `K`, every term of the tower does.
* `Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_of_filtration`: the
  same vanishing for a sheaf of modules carrying a finite filtration whose quotients have it.

## Implementation notes

The triangle is `CategoryTheory.ShortComplex.ShortExact.singleTriangle` of the short exact
sequence, which has the three terms placed in degree zero, carried along the triangulated
functor `K ⊗^L_O -`. Exactness of that functor is the `exact_right` field of
`Stacks.SheafOfModules.DerivedTensorProduct`, an instance, so `Functor.map_distinguished`
applies with no further argument.

The tower is presented as a family of short exact sequences together with isomorphisms of their
middle and right terms with the members of the family, rather than by asking the middle and
right terms to *be* those members. That is what makes the statement applicable to a filtration
whose quotients are only canonically isomorphic to the intended objects, which is the situation
of a tower of quotients by the powers of a sheaf of ideals.

The two induction principles run along the tower in opposite directions, and that is forced by
which vertex of the triangle the conclusion sits on. An upper bound propagates to the *third*
vertex as well as to the second, so the tower of quotients `O/Iⁿ⁺¹ ↠ O/Iⁿ` can be climbed with
the unknown term in the middle and the known one on the right. A vanishing in a single degree
propagates only to the *second* vertex — the cohomology of the first and third vertices in a
single degree is caught between neighbouring degrees of the other two — so
`isZero_homology_tensor_single_of_tower` is stated for an increasing tower, with the unknown
term again in the middle but the known one now on the left. That is the direction a finite
filtration `0 ⊂ Iᵐ⁻¹F ⊂ … ⊂ IF ⊂ F` is traversed in.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, w, d} X)
  (K : RingedSite.DerivedModules.{u, v, w, d} X)

/-- **The derived tensor product of an object of `D(O)` with a short exact sequence of sheaves
of `O`-modules is a distinguished triangle.** Tensoring in the second variable is an exact
functor of triangulated categories, and the three terms of a short exact sequence placed in
degree zero form a distinguished triangle. -/
theorem mapTriangle_singleTriangle_distinguished
    {S : ShortComplex (RingedSite.Modules.{u, v, w} X)} (hS : S.ShortExact) :
    (T.tensor.obj K).mapTriangle.obj hS.singleTriangle ∈
      distTriang (RingedSite.DerivedModules.{u, v, w, d} X) :=
  (T.tensor.obj K).map_distinguished _ hS.singleTriangle_distinguished

/-- The isomorphism `K ⊗^L_O F[0] ≅ K ⊗^L_O F'[0]` induced by an isomorphism `F ≅ F'`. -/
private def tensorSingleIso {F F' : RingedSite.Modules.{u, v, w} X} (e : F ≅ F') :
    (T.tensor.obj K).obj ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F)
      ≅ (T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F') :=
  (T.tensor.obj K).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso e)

/-- **A uniform upper bound along a tower of short exact sequences.** Let `M : ℕ → Mod(O)` and
let `0 → (S n).X₁ → M (n + 1) → M n → 0` be short exact for every `n`. If `K ⊗^L_O M 0` and all
the `K ⊗^L_O (S n).X₁` are bounded above by `b`, then the family `K ⊗^L_O M n` is uniformly
bounded above by `b`. -/
theorem isUniformlyBoundedAbove_tensor_of_tower
    (M : ℕ → RingedSite.Modules.{u, v, w} X) (b : ℤ)
    (S : ℕ → ShortComplex (RingedSite.Modules.{u, v, w} X))
    (hS : ∀ n, (S n).ShortExact)
    (e₂ : ∀ n, (S n).X₂ ≅ M (n + 1)) (e₃ : ∀ n, (S n).X₃ ≅ M n)
    (h0 : Stacks.DerivedCategory.IsBoundedAboveBy
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj (M 0))) b)
    (h₁ : ∀ n, Stacks.DerivedCategory.IsBoundedAboveBy
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj (S n).X₁)) b) :
    Stacks.DerivedCategory.IsUniformlyBoundedAbove
      (fun n : ℕ => (T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj (M n))) :=
  Stacks.DerivedCategory.isUniformlyBoundedAbove_of_triangles _ b h0
    (fun n => (T.tensor.obj K).mapTriangle.obj (hS n).singleTriangle)
    (fun n => mapTriangle_singleTriangle_distinguished T K (hS n)) h₁
    (fun n => tensorSingleIso T K (e₂ n)) (fun n => tensorSingleIso T K (e₃ n))

/-- The cohomology of `K ⊗^L_O F[0]` in the degree `i`, the object whose vanishing the
dévissage below propagates. -/
abbrev homologyTensorSingle (i : ℤ) (F : RingedSite.Modules.{u, v, w} X) :
    RingedSite.Modules.{u, v, w} X :=
  (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).obj
    ((T.tensor.obj K).obj
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F))

/-- **Degreewise vanishing passes to the middle term of a short exact sequence.** The cohomology
of `K ⊗^L_O (S.X₂)[0]` in a degree is caught between that of `K ⊗^L_O (S.X₁)[0]` and that of
`K ⊗^L_O (S.X₃)[0]` in the same degree, by the long exact sequence of the distinguished triangle
of `S`.

Unlike an upper bound, a vanishing in a *single* degree propagates to the second vertex of a
distinguished triangle only: the first and third vertices see the neighbouring degrees of the
other two as well. -/
theorem isZero_homology_tensor_single_X₂ (i : ℤ)
    {S : ShortComplex (RingedSite.Modules.{u, v, w} X)} (hS : S.ShortExact)
    (h₁ : IsZero (homologyTensorSingle T K i S.X₁))
    (h₃ : IsZero (homologyTensorSingle T K i S.X₃)) :
    IsZero (homologyTensorSingle T K i S.X₂) :=
  ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) 0).homologySequence_exact₂
    ((T.tensor.obj K).mapTriangle.obj hS.singleTriangle)
    (mapTriangle_singleTriangle_distinguished T K hS) i).isZero_X₂
      (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

/-- Vanishing of the cohomology of `K ⊗^L_O F[0]` transports along an isomorphism of `F`. -/
theorem isZero_homologyTensorSingle_of_iso (i : ℤ)
    {F F' : RingedSite.Modules.{u, v, w} X} (e : F ≅ F')
    (h : IsZero (homologyTensorSingle T K i F')) :
    IsZero (homologyTensorSingle T K i F) :=
  h.of_iso ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).mapIso
    (tensorSingleIso T K e))

/-- **Degreewise vanishing along an increasing tower of short exact sequences.** Let
`M : ℕ → Mod(O)` and let `0 → M n → M (n + 1) → (S n).X₃ → 0` be short exact for every `n`. If
the cohomology of `K ⊗^L_O M 0` in the degree `i` vanishes, and so does that of every
`K ⊗^L_O (S n).X₃`, then so does that of every `K ⊗^L_O M n`. -/
theorem isZero_homology_tensor_single_of_tower (i : ℤ)
    (M : ℕ → RingedSite.Modules.{u, v, w} X)
    (S : ℕ → ShortComplex (RingedSite.Modules.{u, v, w} X))
    (hS : ∀ n, (S n).ShortExact)
    (e₁ : ∀ n, (S n).X₁ ≅ M n) (e₂ : ∀ n, (S n).X₂ ≅ M (n + 1))
    (h0 : IsZero (homologyTensorSingle T K i (M 0)))
    (h₃ : ∀ n, IsZero (homologyTensorSingle T K i (S n).X₃))
    (n : ℕ) :
    IsZero (homologyTensorSingle T K i (M n)) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    exact isZero_homologyTensorSingle_of_iso T K i (e₂ n).symm
      (isZero_homology_tensor_single_X₂ T K i (hS n)
        (isZero_homologyTensorSingle_of_iso T K i (e₁ n) ih) (h₃ n))

/-- **Degreewise vanishing along a finite filtration.** Let `A : ℕ → Mod(O)` be a filtration,
presented as a family of monomorphisms `u k : A (k + 1) ⟶ A k`, which reaches zero at the stage
`m`. If the cohomology of `K ⊗^L_O (A k / A (k + 1))[0]` in the degree `i` vanishes for every
`k`, then so does that of `K ⊗^L_O (A 0)[0]`.

This is the step "`F` has a finite filtration whose successive quotients are `O/I`-modules,
so it suffices to treat the quotients" of the proof of Stacks 0942 part (2), with the
`O/I`-module hypothesis replaced by the vanishing it is used for. The filtration is given by
monomorphisms rather than by submodules of `A 0`, so that the `I`-adic filtration
`0 ⊂ Iᵐ⁻¹F ⊂ … ⊂ IF ⊂ F` can be supplied with its own inclusions. -/
theorem isZero_homology_tensor_single_of_filtration (i : ℤ) (m : ℕ)
    (A : ℕ → RingedSite.Modules.{u, v, w} X)
    (u : ∀ k : ℕ, A (k + 1) ⟶ A k) (hu : ∀ k, Mono (u k)) (hm : IsZero (A m))
    (hgr : ∀ k : ℕ, IsZero (homologyTensorSingle T K i (cokernel (u k)))) :
    IsZero (homologyTensorSingle T K i (A 0)) := by
  have key : ∀ k : ℕ, IsZero (homologyTensorSingle T K i (A (m - k))) := by
    intro k
    induction k with
    | zero =>
      exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ hm))
    | succ k ih =>
      rcases Nat.lt_or_ge k m with hk | hk
      · have h₁ : m - k = (m - k - 1) + 1 := by omega
        have h₂ : m - (k + 1) = m - k - 1 := by omega
        rw [h₁] at ih
        rw [h₂]
        have := hu (m - k - 1)
        exact isZero_homology_tensor_single_X₂ T K i
          (ShortComplex.shortExact_mk_cokernel_π (u (m - k - 1))) ih (hgr (m - k - 1))
      · have h : m - (k + 1) = m - k := by omega
        rw [h]
        exact ih
  simpa using key m

end Stacks.SheafOfModules.DerivedTensorProduct

end
