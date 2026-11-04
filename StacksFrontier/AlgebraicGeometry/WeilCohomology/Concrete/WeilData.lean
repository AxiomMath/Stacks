module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistedInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Monoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.PoincareDuality

/-!
# Weil cohomology theories, I: the data (D0)–(D3) and the axioms (A), (B), (C)

Section 45.9 of the Stacks Project (Tag 0FHA) fixes a field `k`, a field `F` of characteristic
zero, and data

* (D0) a one-dimensional `F`-vector space `F(1)`;
* (D1) a contravariant functor `H^*` from the category of smooth projective schemes over `k` to
  the category of graded commutative `F`-algebras;
* (D2) for every smooth projective `X` over `k` a group homomorphism `γ : CH^i(X) → H^{2i}(X)(i)`;
* (D3) for every nonempty smooth projective `X` over `k`, equidimensional of dimension `d`, a map
  `∫_X : H^{2d}(X)(d) → F`,

and the axioms (A) Poincaré duality, (B) the Künneth formula, (C) compatibility with cycle
classes. This file writes them down over the actual category of smooth projective schemes over
`k`, with the actual Chow groups `CH^i(X) = ∏_d CH_{d-i}(X_d)` and the actual Gysin maps,
intersection products and proper pushforwards of Chapter 42. Every axiom, and every clause of
an axiom, is its own `Prop`, so that a statement assuming only some of them (e.g. "(A), (B) and
(C)(a)") can say so.

## The interface decisions

1. *"`X` is nonempty and equidimensional of dimension `d`"* is
   `Stacks.WeilCohomology.IsNonemptyEquidimensional X d`: `X` is nonempty and its structure
   morphism has relative dimension `d` (`AlgebraicGeometry.RelativeDimension`, Stacks 02NJ (3)).
   Equidimensionality alone, which the empty scheme satisfies, is
   `AlgebraicGeometry.RelativeDimension X.obj.hom d`.
2. *`∫_X`* is the field `WeilData.trace X d hX` of the data; it takes the proof
   `hX : IsNonemptyEquidimensional X d` as an argument. `d` is a natural number.
3. *`CH^i(X)`* is `Stacks.Chow.codimensionChowGroup k X.obj.hom i = ∏_d CH_{d-i}(X_d)`, with
   integer coefficients, as in Chow Homology, Section 0FE2 (cited by the conventions of the
   chapter, Section 0FFI); `X_d` is the open and closed part `Stacks.WeilCohomology.dimPart` of
   `X` of dimension `d` (Stacks 02NM). This is the group on which the Gysin map and the
   intersection product of Chapter 42 are formed (`Stacks.Chow.codimensionGysin`,
   `Stacks.Chow.codimensionIntersectionProduct`). No `⊗ ℚ`: (D2) is a group homomorphism on the
   integral Chow group.
4. *Products.* `SmoothProjectiveScheme.prod X Y` is defined as the tensor product `X ⊗ Y` of
   the symmetric monoidal structure of `Concrete/Monoidal.lean`, and
   `SmoothProjectiveScheme.point k` as its unit `𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)`,
   so that there is one construction of each. Its underlying scheme is the fibre product
   `X ×_{Spec k} Y` and its structure morphism is `Stacks.WeilCohomology.prodBase` (first
   projection followed by the structure morphism of `X`, as in the correspondences of Section
   0FFZ), both by `rfl`; the unit is `Spec k` with its identity. `fst`, `snd` are the projections
   and `diag X : X ⟶ X × X` the diagonal. The comparisons with the monoidal structure
   (`prod_eq_tensorObj`, `point_eq_tensorUnit`, `prodMap f g = f ⊗ₘ g`, the constraints, the
   cartesian projections of `Over (Spec k)`) are in `Concrete/ProdTensorBridge.lean`; they hold by
   `rfl` at default transparency but not at reducible transparency, so `rw` and `simp` need them
   to pass between `prod X Y` and `X ⊗ Y`.
5. *(D1)* `H X` is an `F`-algebra (a ring) with a `GradedAlgebra` structure
   `grade X : ℤ → Submodule F (H X)` and the Koszul sign rule; pullback `pull f` is an
   `F`-algebra homomorphism preserving the grading. The total cohomology `H X` is a ring.
   `H^n(X)(m)` is `WeilData.Tw X n m = H^n(X) ⊗_F F(m)`, the tensor-defined Tate twist
   `Stacks.WeilCohomology.tateTwist`.
6. *(D2)* `WeilData.cycleClass X i : CH^i(X) →+ H^{2i}(X)(i)`; *(D3)* `WeilData.trace`;
   *(A)* `WeilData.FiniteDimensionality` and `WeilData.PerfectPairing`, bundled as
   `WeilData.PoincareDuality`. The pairing of (A)(b) is `WeilData.pairing`, stated for any
   `i + j = 2d` rather than with `j` written `2d - i`. The pushforward on cohomology is
   `WeilData.pushforward`, the contragredient of pullback, with its trace equation
   `WeilData.pushforward_trace`; it is defined for every degree and twist.
7. *(B)(a)* `WeilData.KunnethIsomorphism`: bijectivity of `WeilData.kunnethMap`,
   `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`. *(B)(b)* `WeilData.KunnethTrace`: `∫_{X×Y} = ∫_X ⊗ ∫_Y` via (a),
   i.e. `∫_{X×Y}(pr₁^*a ∪ pr₂^*b) = ∫_X a · ∫_Y b` for `a ∈ H^{2d}(X)(d)`, `b ∈ H^{2e}(Y)(e)`, and
   `∫_{X×Y}(pr₁^*a ∪ pr₂^*b) = 0` on the other Künneth components of `H^{2(d+e)}(X × Y)(d+e)`,
   where `∫_X ⊗ ∫_Y` vanishes, the trace maps being zero outside their degree (the convention
   the chapter makes explicit in "Ad (A6)"). It is quantified over a proof that `X × Y` is
   nonempty equidimensional of dimension `d + e`; the trace does not depend on that proof.
8. *(C)* `WeilData.CycleClassPullback` (C)(a), with `f^!` the Gysin map of Stacks 0FF3 of the
   morphism `f` of schemes smooth over `k`, acting on codimension-graded classes
   (`Stacks.Chow.codimensionGysin`); `WeilData.CycleClassPushforward` (C)(b),
   with `f_*` the proper pushforward `CH_i(X) → CH_i(Y)` read as
   `CH^{d-i}(X) → CH^{e-i}(Y)` (`Stacks.WeilCohomology.equidimensionalPushforward`);
   `WeilData.CycleClassMul` (C)(c) with the intersection product of Stacks 0FC0
   (`Stacks.Chow.codimensionIntersectionProduct`); `WeilData.CycleClassPoint` (C)(d), with
   `[Spec k]` the fundamental class `Stacks.WeilCohomology.fundamentalClass`. They are bundled
   as `WeilData.CycleClassAxiom`. The comparison `f^! = f^*` for flat `f` is Stacks 0FF4
   (`Stacks.Chow.lciGysinMap` and flat pullback); its codimension-graded form
   for open immersions and coprojections is not part of this file.
9. Comparing `CH^d(X)` over `k` with `Stacks.Chow.chowGroup (fieldChowSituation k') _ 0` for `X`
   over a finite separable `k'/k` is not part of this file.

## Main definitions

* `Stacks.WeilCohomology.WeilData`: the data (D0), (D1), (D2), (D3).
* `Stacks.WeilCohomology.WeilData.H0`, `Stacks.WeilCohomology.WeilData.H0.algebraOfHom`: the
  commutative `F`-algebra `H^0(X)`, and the `H^0(Y)`-algebra structure on `H^*(X)` given by `f^*`.
* `Stacks.WeilCohomology.WeilData.PoincareDuality`: axiom (A).
* `Stacks.WeilCohomology.WeilData.Kunneth`: axiom (B).
* `Stacks.WeilCohomology.WeilData.CycleClassAxiom`: axiom (C).

## References

* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
* [Stacks Project, Section 45.2 (Tag 0FFI)](https://stacks.math.columbia.edu/tag/0FFI)
* [Stacks Project, Section 42.33 (Tag 0FE2)](https://stacks.math.columbia.edu/tag/0FE2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

/-! ### Products, the point, and equidimensionality -/

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- **The product `X × Y = X ×_{Spec k} Y`** of two smooth projective schemes over `k`: the
tensor product `X ⊗ Y` of `Concrete/Monoidal.lean`. Its underlying scheme is the fibre product
`X ×_{Spec k} Y` and its structure morphism is `X ×_k Y ⟶ X ⟶ Spec k` (both by `rfl`); it is
smooth (base change and composition) and H-projective (Stacks 01WF and 01WE). -/
def prod (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (SmoothProjectiveScheme k).FullSubcategory :=
  MonoidalCategory.tensorObj X Y

/-- The first projection `pr₁ : X × Y ⟶ X`. -/
def fst (X Y : (SmoothProjectiveScheme k).FullSubcategory) : prod X Y ⟶ X :=
  ObjectProperty.homMk (Over.homMk (pullback.fst X.obj.hom Y.obj.hom) rfl)

/-- The second projection `pr₂ : X × Y ⟶ Y`. -/
def snd (X Y : (SmoothProjectiveScheme k).FullSubcategory) : prod X Y ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.snd X.obj.hom Y.obj.hom) pullback.condition.symm)

/-- The diagonal `Δ : X ⟶ X × X`. -/
def diag (X : (SmoothProjectiveScheme k).FullSubcategory) : X ⟶ prod X X :=
  ObjectProperty.homMk (Over.homMk (pullback.diagonal X.obj.hom) (by
    change pullback.diagonal X.obj.hom ≫ pullback.fst _ _ ≫ X.obj.hom = X.obj.hom
    rw [pullback.diagonal_fst_assoc]))

/-- The underlying morphism of schemes of `fst X Y` is `pullback.fst`. -/
@[simp]
theorem fst_left (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (fst X Y).hom.left = pullback.fst X.obj.hom Y.obj.hom := rfl

/-- The underlying morphism of schemes of `snd X Y` is `pullback.snd`. -/
@[simp]
theorem snd_left (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (snd X Y).hom.left = pullback.snd X.obj.hom Y.obj.hom := rfl

/-- The underlying morphism of schemes of `diag X` is `pullback.diagonal`. -/
@[simp]
theorem diag_left (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (diag X).hom.left = pullback.diagonal X.obj.hom := rfl

variable (k) in
/-- **The point `Spec k`** as a smooth projective scheme over `k`: the unit
`𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)` of `Concrete/Monoidal.lean`, the scheme `Spec k`
with the identity as structure morphism (by `rfl`). -/
def point : (SmoothProjectiveScheme k).FullSubcategory :=
  MonoidalCategory.tensorUnit _

end SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- A morphism of smooth projective schemes over `k` is locally of finite type. -/
instance locallyOfFiniteType_hom_left {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) :
    LocallyOfFiniteType f.hom.left := by
  have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by rw [Over.w f.hom]; infer_instance
  exact LocallyOfFiniteType.of_comp (f := f.hom.left) (g := Y.obj.hom) inferInstance

/-- **`X` is nonempty and equidimensional of dimension `d`**: the underlying scheme is nonempty
and the structure morphism has relative dimension `d` (Stacks 02NJ (3)); over a field this says
that `X` is equidimensional of dimension `d`. -/
structure IsNonemptyEquidimensional (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ) : Prop where
  /-- The underlying scheme of `X` is nonempty. -/
  nonempty : Nonempty X.obj.left
  /-- The structure morphism of `X` has relative dimension `d`. -/
  relativeDimension : RelativeDimension X.obj.hom d

/-- `Spec k` is nonempty and equidimensional of dimension `0`. -/
theorem isNonemptyEquidimensional_point : IsNonemptyEquidimensional
    (SmoothProjectiveScheme.point k) 0 where
  nonempty := show Nonempty (Spec (.of k)) from inferInstance
  relativeDimension := relativeDimension_of_isIso (𝟙 (Spec (.of k)))

/-! ### Chow groups of a smooth projective scheme -/

/-- **The fundamental class `[X] = ∑_d [X_d]_d ∈ CH^0(X)`** of a smooth projective scheme
(Chow Homology, Remark 0FE4). -/
def fundamentalClass
    (X : (SmoothProjectiveScheme k).FullSubcategory) : codimensionChowGroup k X.obj.hom 0 :=
  fun d ↦ chowGroupDegreeEquiv _ _ (sub_zero (d : ℤ)).symm
    (fundamentalChowClass (fieldChowSituation k) (partBase X.obj.hom d) d)

/-- **Proper pushforward `f_* : CH^p(X) → CH^q(Y)` for `X`, `Y` equidimensional of dimensions `d`
and `e`, `q = p + e - d`.** On Chow groups graded by dimension it is proper pushforward
`CH_{d-p}(X) → CH_{d-p}(Y)` (`f` is proper, `X` being proper over `k` and `Y` separated), read
through `CH^p(X) = CH_{d-p}(X_d)` and `CH^q(Y) = CH_{e-q}(Y_e)`: the class `α_d ∈ CH_{d-p}(X_d)`
is pushed forward along `X_d ⟶ X ⟶ Y` and restricted to `Y_e`. When `X` and `Y` are
equidimensional of dimensions `d` and `e` the other parts are empty, and this is the pushforward
of axiom (C)(b). -/
def equidimensionalPushforward {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (d e : ℕ)
    (p q : ℤ) (h : q = p + e - d) :
    codimensionChowGroup k X.obj.hom p →+ codimensionChowGroup k Y.obj.hom q :=
  haveI : IsProper f.hom.left := by
    have : IsProper (f.hom.left ≫ Y.obj.hom) := by rw [Over.w f.hom]; infer_instance
    exact IsProper.of_comp f.hom.left Y.obj.hom
  haveI := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
  AddMonoidHom.pi fun e' ↦
    if he : e' = e then
      (chowGroupDegreeEquiv _ _ (by subst he; omega)).toAddMonoidHom.comp <|
        (chowGroupRestrict (fieldChowSituation k) Y.obj.hom (partBase Y.obj.hom e')
          (dimPart Y.obj.hom e').ι rfl (d - p)).comp <|
        (properChowPushforward (fieldChowSituation k) (partBase X.obj.hom d) Y.obj.hom
          ((dimPart X.obj.hom d).ι ≫ f.hom.left) (by rw [Category.assoc, Over.w f.hom]) (d - p)
          (properPushforwardDescends _ _ _ _ _ _)).comp <|
        Pi.evalAddMonoidHom (fun d' : ℕ ↦ chowGroup (fieldChowSituation k)
          (partBase X.obj.hom d') (d' - p)) d
    else 0

/-! ### The data -/

variable (k) in
/-- **The data (D0), (D1), (D2), (D3) of Section 45.9 (Tag 0FHA).**

* (D0) a one-dimensional `F`-vector space `F(1)`, the field `tate`;
* (D1) a contravariant functor `X ↦ H^*(X)` from smooth projective schemes over `k` to `𝐙`-graded
  graded commutative `F`-algebras: an `F`-algebra `H X` with a grading
  `H X = ⨁_{n ∈ 𝐙} grade X n` obeying the Koszul rule, and pullbacks `pull f` which are graded
  `F`-algebra homomorphisms, functorially;
* (D2) for every `X` and `i` a group homomorphism `γ : CH^i(X) → H^{2i}(X)(i)`;
* (D3) for every nonempty `X` equidimensional of dimension `d` a map `∫_X : H^{2d}(X)(d) → F`. -/
structure WeilData (F : Type w) [Field F] where
  /-- (D0) The Tate line `F(1)`. -/
  tate : Type w
  [addCommGroup_tate : AddCommGroup tate]
  [module_tate : Module F tate]
  /-- (D0) `F(1)` is one-dimensional. -/
  finrank_tate : Module.finrank F tate = 1
  /-- (D1) The cohomology `H^*(X)`. -/
  H : (SmoothProjectiveScheme k).FullSubcategory → Type w
  [ring : ∀ X, Ring (H X)]
  [algebra : ∀ X, Algebra F (H X)]
  /-- (D1) The grading `H^*(X) = ⨁_{n ∈ 𝐙} H^n(X)`. -/
  grade : ∀ X, ℤ → Submodule F (H X)
  [gradedAlgebra : ∀ X, _root_.GradedAlgebra (grade X)]
  /-- (D1) The cup product is graded commutative. -/
  graded_comm : ∀ (X) (i j : ℤ) (a b : H X), a ∈ grade X i → b ∈ grade X j →
    a * b = (Int.negOnePow (i * j) : ℤ) • (b * a)
  /-- (D1) The pullback `f^* : H^*(Y) → H^*(X)`. -/
  pull : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory}, (X ⟶ Y) → (H Y →ₐ[F] H X)
  pull_id : ∀ X, pull (𝟙 X) = AlgHom.id F (H X)
  pull_comp : ∀ {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z),
    pull (f ≫ g) = (pull f).comp (pull g)
  /-- (D1) Pullback preserves the grading. -/
  pull_grade : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ) (a : H Y),
    a ∈ grade Y n → pull f a ∈ grade X n
  /-- (D2) The cycle class map `γ : CH^i(X) → H^{2i}(X)(i)`. -/
  cycleClass : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ),
    codimensionChowGroup k X.obj.hom i →+ tateTwist F tate (grade X (2 * i)) i
  /-- (D3) The trace map `∫_X : H^{2d}(X)(d) → F`. -/
  trace : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ),
      IsNonemptyEquidimensional X d →
    (tateTwist F tate (grade X (2 * (d : ℤ))) d →ₗ[F] F)

attribute [instance] WeilData.addCommGroup_tate WeilData.module_tate WeilData.ring
  WeilData.algebra WeilData.gradedAlgebra

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-- `H^n(X)(m) = H^n(X) ⊗_F F(m)`. -/
abbrev Tw (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) : ModuleCat.{w} F :=
  tateTwist F W.tate (W.grade X n) m

/-- The cup product `H^i(X) × H^j(X) → H^n(X)` for `i + j = n`. -/
def cup (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ) (h : i + j = n) :
    W.grade X i →ₗ[F] W.grade X j →ₗ[F] W.grade X n :=
  LinearMap.mk₂ F (fun a b ↦ ⟨a * b, h ▸ SetLike.GradedMul.mul_mem a.2 b.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

/-- The cup product of `a ∈ H^i(X)` and `b ∈ H^j(X)` is their product in `H^*(X)`. -/
@[simp]
theorem coe_cup (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ) (h : i + j = n)
    (a : W.grade X i)
    (b : W.grade X j) : (W.cup X i j n h a b : W.H X) = a * b := rfl

/-- The twisted cup product `H^i(X)(s) × H^j(X)(t) → H^n(X)(m)` for `i + j = n`, `s + t = m`. -/
def cupTw (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ) (h : i + j = n) (s t m : ℤ)
    (h' : s + t = m) : W.Tw X i s →ₗ[F] W.Tw X j t →ₗ[F] W.Tw X n m :=
  tateCup W.finrank_tate (W.cup X i j n h) s t m h'

/-- The pullback `f^* : H^n(Y) → H^n(X)`. -/
def pullDeg {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ) :
    W.grade Y n →ₗ[F] W.grade X n :=
  (W.pull f).toLinearMap.restrict (W.pull_grade f n)

/-- The pullback `f^* : H^n(Y)(m) → H^n(X)(m)`. -/
def pullTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n m : ℤ) :
    W.Tw Y n m →ₗ[F] W.Tw X n m :=
  tateTwistMap (W.pullDeg f n) m

/-! ### Degree zero -/

/-- **`H^0(X)`**, the degree-zero part of `H^*(X)`, as an `F`-subalgebra. -/
abbrev H0 (X : (SmoothProjectiveScheme k).FullSubcategory) : Subalgebra F (W.H X) :=
  SetLike.GradeZero.subalgebra (W.grade X)

/-- Degree-zero classes are central in `H^*(X)`: graded commutativity at `i = 0`. -/
theorem mul_comm_of_mem_grade_zero (X : (SmoothProjectiveScheme k).FullSubcategory) {c : W.H X}
    (hc : c ∈ W.grade X 0) (x : W.H X) : c * x = x * c := by
  induction x using DirectSum.Decomposition.inductionOn (W.grade X) with
  | zero => simp
  | homogeneous hx =>
    rw [W.graded_comm X 0 _ c _ hc hx.2]
    simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

/-- `H^0(X)` is commutative. -/
instance (X : (SmoothProjectiveScheme k).FullSubcategory) : CommRing (W.H0 X) :=
  { (inferInstance : Ring (W.H0 X)) with
    mul_comm := fun a b ↦ Subtype.ext (W.mul_comm_of_mem_grade_zero X a.2 b) }

/-- **The `H^0(Y)`-algebra structure on `H^*(X)` induced by `f^*`** for `f : X ⟶ Y`; it is an
algebra structure because `f^*` maps `H^0(Y)` into the centre `H^0(X)`. -/
@[instance_reducible]
def H0.algebraOfHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) : Algebra
    (W.H0 Y) (W.H X) :=
  RingHom.toAlgebra' ((W.pull f).toRingHom.comp (W.H0 Y).val.toRingHom) fun c x ↦
    W.mul_comm_of_mem_grade_zero X (W.pull_grade f 0 c c.2) x

/-- For the algebra structure `H0.algebraOfHom W f`, the algebra map `H^0(Y) → H^*(X)` is `f^*`. -/
theorem H0.algebraOfHom_algebraMap {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    (c : W.H0 Y) :
    (letI := H0.algebraOfHom W f; algebraMap (W.H0 Y) (W.H X) c) = W.pull f c :=
  rfl

/-! ### Axiom (A): Poincaré duality -/

/-- The pairing `H^i(X) × H^j(X)(d) → H^{2d}(X)(d) → F`, `(a, b) ↦ ∫_X a ∪ b`, for `i + j = 2d`. -/
def pairing (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d)
    (i j : ℤ) (h : i + j = 2 * d) : W.grade X i →ₗ[F] W.Tw X j d →ₗ[F] F :=
  (tateCupLeft (W.cup X i j _ h) d).compr₂ (W.trace X d hX)

/-- The pairing `H^i(X)(s) × H^j(X)(t) → H^{2d}(X)(d) → F` at arbitrary complementary degrees and
twists, `i + j = 2d` and `s + t = d`. -/
def pairingTw (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d)
    (i j : ℤ) (h : i + j = 2 * d) (s t : ℤ) (h' : s + t = d) :
    W.Tw X i s →ₗ[F] W.Tw X j t →ₗ[F] F :=
  (W.cupTw X i j _ h s t d h').compr₂ (W.trace X d hX)

/-- **Axiom (A)(a)**: for `X` nonempty, equidimensional of dimension `d`, `dim_F H^i(X) < ∞` for
all `i`. -/
def FiniteDimensionality : Prop :=
  ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ), IsNonemptyEquidimensional X d →
    ∀ i : ℤ, FiniteDimensional F (W.grade X i)

/-- **Axiom (A)(b)**: for `X` nonempty, equidimensional of dimension `d`,
`H^i(X) × H^{2d-i}(X)(d) → H^{2d}(X)(d) → F` is a perfect pairing for all `i`, the final map being
the trace map `∫_X`. -/
def PerfectPairing : Prop :=
  ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) (hX : IsNonemptyEquidimensional X d)
      (i j : ℤ)
    (h : i + j = 2 * d), (W.pairing X d hX i j h).IsPerfPair

/-- **Axiom (A), Poincaré duality.** -/
structure PoincareDuality : Prop where
  /-- (A)(a): the cohomology groups `H^i(X)` are finite dimensional. -/
  finiteDimensionality : W.FiniteDimensionality
  /-- (A)(b): the pairings `H^i(X) × H^{2d-i}(X)(d) → F` are perfect. -/
  perfectPairing : W.PerfectPairing

variable {W}

/-- Under (A)(b) the pairings at arbitrary twists are perfect. -/
theorem PerfectPairing.pairingTw (hA : W.PerfectPairing)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) (s t : ℤ)
    (h' : s + t = d) : (W.pairingTw X d hX i j h s t h').IsPerfPair :=
  have : ((tateCupLeft (W.cup X i j _ h) d).compr₂ (W.trace X d hX)).IsPerfPair :=
    hA X d hX i j h
  tateCup_isPerfPair W.finrank_tate (W.cup X i j _ h) d (W.trace X d hX) s t h'

variable (W)

/-- **The pushforward `f_* : H^j(X)(t) → H^{j'}(Y)(t')`** of a morphism `f : X ⟶ Y` of nonempty
equidimensional smooth projective schemes of dimensions `d` and `e`, for `j' = j + 2(e - d)` and
`t' = t + (e - d)`: the contragredient, with respect to the pairings of (A), of
`f^* : H^{2d-j}(Y)(d-t) → H^{2d-j}(X)(d-t)`. In the source's notation, with `i = 2d - j`, this is
`f_* : H^{2d-i}(X)(d) → H^{2e-i}(Y)(e)` twisted by `t - d`. It is characterised by
`∫_X f^*b ∪ a = ∫_Y b ∪ f_*a` (`WeilData.pushforward_trace`). -/
def pushforward (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (j t j' t' : ℤ)
    (hj : j' + 2 * d = j + 2 * e) (ht : t' + d = t + e) : W.Tw X j t →ₗ[F] W.Tw Y j' t' :=
  haveI := hA.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega)
  poincareDualPushforward (W.pairingTw X d hX (2 * d - j) j (by omega) (d - t) t (by omega))
    (W.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega))
    (W.pullTw f (2 * d - j) (d - t))

/-- **The trace equation** `∫_X f^*b ∪ a = ∫_Y b ∪ f_*a` characterising the pushforward. -/
theorem pushforward_trace (hA : W.PerfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y)
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (j t j' t' : ℤ) (hj : j' + 2 * d = j + 2 * e) (ht : t' + d = t + e)
    (b : W.Tw Y (2 * d - j) (d - t)) (a : W.Tw X j t) :
    W.pairingTw X d hX (2 * d - j) j (by omega) (d - t) t (by omega) (W.pullTw f _ _ b) a =
      W.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega) b
        (W.pushforward hA f hX hY j t j' t' hj ht a) :=
  by
  have := hA.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega)
  exact poincareDualPushforward_pairing _ _ _ b a

/-- The trace equation determines the pushforward. -/
theorem eq_pushforward_iff (hA : W.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (j t j' t' : ℤ) (hj : j' + 2 * d = j + 2 * e) (ht : t' + d = t + e)
    (g : W.Tw X j t →ₗ[F] W.Tw Y j' t') :
    g = W.pushforward hA f hX hY j t j' t' hj ht ↔
      ∀ (b : W.Tw Y (2 * d - j) (d - t)) (a : W.Tw X j t),
        W.pairingTw X d hX (2 * d - j) j (by omega) (d - t) t (by omega) (W.pullTw f _ _ b) a =
          W.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega) b (g a) :=
  by
  have := hA.pairingTw Y e hY (2 * d - j) j' (by omega) (d - t) t' (by omega)
  exact eq_poincareDualPushforward_iff _ _ _ g

/-! ### Axiom (B): the Künneth formula -/

/-- The Künneth map `H^*(X) ⊗_F H^*(Y) → H^*(X × Y)`, `a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`. -/
def kunnethMap (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    W.H X ⊗[F] W.H Y →ₗ[F] W.H (SmoothProjectiveScheme.prod X Y) :=
  TensorProduct.lift ((LinearMap.mul F _).compl₁₂
    (W.pull (SmoothProjectiveScheme.fst X Y)).toLinearMap
    (W.pull (SmoothProjectiveScheme.snd X Y)).toLinearMap)

/-- The Künneth map sends `a ⊗ b` to `pr₁^*a ∪ pr₂^*b`. -/
@[simp]
theorem kunnethMap_tmul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (a : W.H X) (b : W.H Y) :
    W.kunnethMap X Y (a ⊗ₜ b) =
      W.pull (SmoothProjectiveScheme.fst X Y) a * W.pull (SmoothProjectiveScheme.snd X Y) b :=
  rfl

/-- **Axiom (B)(a)**: `H^*(X) ⊗_F H^*(Y) → H^*(X × Y)`, `α ⊗ β ↦ pr₁^*α ∪ pr₂^*β` is an
isomorphism. -/
def KunnethIsomorphism : Prop :=
  ∀ X Y : (SmoothProjectiveScheme k).FullSubcategory, Function.Bijective (W.kunnethMap X Y)

/-- **Axiom (B)(b)**: if `X` and `Y` are nonempty and equidimensional, of dimensions `d` and `e`,
then `∫_{X×Y} = ∫_X ⊗ ∫_Y` via (B)(a). On the Künneth component
`H^{2d}(X)(d) ⊗ H^{2e}(Y)(e)` of `H^{2(d+e)}(X × Y)(d + e)` this reads
`∫_{X×Y}(pr₁^*a ∪ pr₂^*b) = ∫_X a · ∫_Y b`; on the other components `H^i(X) ⊗ H^j(Y)`,
`i + j = 2(d + e)`, `i ≠ 2d`, the map `∫_X ⊗ ∫_Y` is zero, the trace maps vanishing outside their
degree. -/
def KunnethTrace : Prop :=
  ∀ (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d e : ℕ)
      (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e)
    (hXY : IsNonemptyEquidimensional (SmoothProjectiveScheme.prod X Y) (d + e)),
    (∀ (a : W.Tw X (2 * d) d) (b : W.Tw Y (2 * e) e),
      W.trace _ (d + e) hXY
        (W.cupTw _ (2 * d) (2 * e) _ (by push_cast; ring) d e _ (by push_cast; ring)
          (W.pullTw (SmoothProjectiveScheme.fst X Y) _ _ a)
          (W.pullTw (SmoothProjectiveScheme.snd X Y) _ _ b)) =
        W.trace X d hX a * W.trace Y e hY b) ∧
    ∀ (i j : ℤ) (h : i + j = 2 * ((d + e : ℕ) : ℤ)), i ≠ 2 * d →
      ∀ (a : W.Tw X i d) (b : W.Tw Y j e),
        W.trace _ (d + e) hXY
          (W.cupTw _ i j _ h d e _ (by push_cast; ring)
            (W.pullTw (SmoothProjectiveScheme.fst X Y) _ _ a)
            (W.pullTw (SmoothProjectiveScheme.snd X Y) _ _ b)) = 0

/-- **Axiom (B), the Künneth formula.** -/
structure Kunneth : Prop where
  /-- (B)(a): the Künneth map is an isomorphism. -/
  kunnethIsomorphism : W.KunnethIsomorphism
  /-- (B)(b): `∫_{X×Y} = ∫_X ⊗ ∫_Y`. -/
  kunnethTrace : W.KunnethTrace

/-! ### Axiom (C): compatibility with cycle classes -/

/-- **Axiom (C)(a)**: for a morphism `f : X → Y` of smooth projective schemes over `k`,
`γ(f^!β) = f^*γ(β)` for `β ∈ CH^*(Y)`, where `f^!` is the Gysin map of Stacks 0FF3. -/
def CycleClassPullback : Prop :=
  ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (i : ℤ)
      (β : codimensionChowGroup k Y.obj.hom i),
    W.cycleClass X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) =
      W.pullTw f _ _ (W.cycleClass Y i β)

/-- **Axiom (C)(b)**: for a morphism `f : X → Y` of nonempty equidimensional smooth projective
schemes over `k`, of dimensions `d` and `e`, `γ(f_*α) = f_*γ(α)` for `α ∈ CH^p(X)`: here
`f_*α ∈ CH^{p+e-d}(Y)` is proper pushforward of cycles and `f_*γ(α)` the pushforward on
cohomology of (A). -/
def CycleClassPushforward (hA : W.PerfectPairing) : Prop :=
  ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (d e : ℕ)
      (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (p q : ℤ) (h : q = p + e - d)
    (α : codimensionChowGroup k X.obj.hom p),
    W.cycleClass Y q (equidimensionalPushforward f d e p q h α) =
      W.pushforward hA f hX hY (2 * p) p (2 * q) q (by omega) (by omega) (W.cycleClass X p α)

/-- **Axiom (C)(c)**: for any smooth projective scheme `X` over `k`,
`γ(α · β) = γ(α) ∪ γ(β)` for `α, β ∈ CH^*(X)`, where `α · β` is the intersection product of
Stacks 0FC0. -/
def CycleClassMul : Prop :=
  ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
      (α : codimensionChowGroup k X.obj.hom i)
    (β : codimensionChowGroup k X.obj.hom j),
    W.cycleClass X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) =
      W.cupTw X (2 * i) (2 * j) _ (by ring) i j _ rfl (W.cycleClass X i α) (W.cycleClass X j β)

/-- **Axiom (C)(d)**: `∫_{Spec k} γ([Spec k]) = 1`. -/
def CycleClassPoint : Prop :=
  W.trace (SmoothProjectiveScheme.point k) 0 isNonemptyEquidimensional_point
    (W.cycleClass (SmoothProjectiveScheme.point k) 0
      (fundamentalClass (SmoothProjectiveScheme.point k))) = 1

/-- **Axiom (C), compatibility with cycle classes**: (C)(a)–(d). Clause (b) uses the pushforward
on cohomology, which is defined using (A)(b). -/
structure CycleClassAxiom (hA : W.PerfectPairing) : Prop where
  /-- (C)(a): `γ(f^!β) = f^*γ(β)`. -/
  pullback : W.CycleClassPullback
  /-- (C)(b): `γ(f_*α) = f_*γ(α)`. -/
  pushforward : W.CycleClassPushforward hA
  /-- (C)(c): `γ(α · β) = γ(α) ∪ γ(β)`. -/
  mul : W.CycleClassMul
  /-- (C)(d): `∫_{Spec k} γ([Spec k]) = 1`. -/
  point : W.CycleClassPoint

end WeilData

end Stacks.WeilCohomology

end
