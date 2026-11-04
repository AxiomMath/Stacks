module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.TensorPowCongrIntBidegree
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPowerPullbackAddIso

/-!
# Pullback commutes with the integer tensor powers multiplicatively

For a morphism of schemes `f : X ⟶ S` and an invertible `𝒪_S`-module `M`,
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso` is the comparison
`f^*(M^{⊗ d}) ≅ (f^*M)^{⊗ d}` in **every integer** degree.  **This file proves that the family is
multiplicative in an arbitrary integer bidegree**, which is what makes it an isomorphism of
`ℤ`-graded `𝒪_X`-algebras `f^*(⨁_{d ∈ ℤ} M^{⊗ d}) ≅ ⨁_{d ∈ ℤ} (f^*M)^{⊗ d}` rather than a
degreewise family of isomorphisms.

Before this the square was available in a bidegree of **natural numbers only**, as
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso`, whose abstract engine
`Stacks.TensorPowerPullbackMul.comparison_mulFamily` is indexed by `ℕ` and inducts on the second
exponent with `Nat.rec`.

## Main definitions

* `Stacks.AlgebraicGeometry.PullbackTensorPowInt.pullbackPowMulIso`: **the multiplication of the
  pulled-back tensor powers**, `f^*(M^{⊗ n}) ⊗ f^*(M^{⊗ m}) ≅ f^*(M^{⊗ (n+m)})` — the comparison of
  [Stacks, Tag 01CD] inverted, followed by `f^*` of the addition law of [Stacks, Tag 01CU].  This
  is the multiplication the comparison family has to carry to
  `Stacks.Ample.tensorPowModuleAddIso` on `X`.
* `Stacks.AlgebraicGeometry.PullbackTensorPowInt.pullbackPowInvIso`: the pulled-back inverse law,
  `f^*(M^{⊗ n}) ⊗ f^*(M^{⊗ (-n)}) ≅ 𝒪_X`, which is the tensor inverse that
  `Stacks.Monoidal.square_step_left` asks for when the chase runs downwards.

## Main results

* `Stacks.AlgebraicGeometry.PullbackTensorPowInt.pullbackTensorPowModuleIntIso_mul`: **the bidegree
  square in an arbitrary integer bidegree**, at the `pullbackPowMulIso` spelling of the
  multiplication on the pullback side.
* `PullbackTensorPowInt.pullbackTensorPowModuleIntIso_tensorPowModuleAddIso`: the same square
  written exactly as the natural-number statement
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso` is written, so that
  the two are visibly the same statement with the restriction on the degrees removed.
* `Stacks.AlgebraicGeometry.PullbackTensorPowInt.intIso_one_eq`: the degree one value of the
  comparison family is `Stacks.RelativeVeryAmple.pullbackPowOneIso`, the normalisation that the
  natural-number file deliberately did not need.
* `Stacks.AlgebraicGeometry.PullbackTensorPowInt.pullbackMul_add_eq_zero`: the inverse-law square,
  at every bidegree summing to zero.

## The route

It is the chase of
`StacksFrontier/AlgebraicGeometry/TwistTensor/TensorPowCongrIntBidegree.lean`, which ran it for the
transport leg, with three differences.

* **The source family's multiplication is not an addition law of tensor powers.**  It is
  `pullbackPowMulIso`, the addition law on `S` conjugated by [Stacks, Tag 01CD], so its
  associativity is not `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int` but that
  constraint pushed through the monoidal functor `f^*`.  That push is
  `Stacks.TensorPowerPullbackMul.laxMul_assoc`, which is stated with `ℕ`-indexed degrees;
  `Stacks.TensorPowerPullbackMul.laxMul_assoc_free` below is its five-rewrite proof restated with
  every object free and a transport of the total degree allowed, which is what an integer tridegree
  needs.  The left unit law is `Stacks.TensorPowerPullbackMul.laxMul_unitor_left`, the mirror of
  `laxMul_unitor`.
* **The natural-number half is reused, not re-proved.**
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso` is the square in a
  bidegree of natural numbers, and the comparison in a nonnegative degree is the natural-number
  comparison by definition, so `pullbackMul_natCast` is that statement retyped.  Only the negative
  degrees are new.
* **The common tensor inverse is on the other side.**  In
  `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleNegSuccIso` the object
  that both negative-degree candidates are tensor inverses of is `(f^*M)^{⊗ (k+1)}`, the power on
  the *target*; in `tensorPowModuleIsoOfIsoNegSucc` it was the power on the source.  So the
  characterising identity
  `Stacks.AlgebraicGeometry.TensorUnitInvLaw.isoOfTensorUnitIso_whiskerRight` hands back a square
  with the comparison in the degree `k + 1` *inverted* on the second factor, and
  `whisker_cancel_to_tensorHom` below cancels it against itself — where the transport leg's chase
  only had to convert a whiskering into a tensor product of morphisms.

Everything else is shared: the four free bookkeeping lemmas
`Stacks.AlgebraicGeometry.TensorPowCongrInt.zero_right_free`, `one_eq_free`,
`inv_law_square_free` and `hom_inv_cancel_free` are consumed from the transport leg's file rather
than restated, and the chase skeleton is
`Stacks.AlgebraicGeometry.ThetaMul.square_step` upwards and
`Stacks.Monoidal.square_step_left_of_mono` downwards.

## Implementation notes

**`letI`, not `have`, for the monoidal structure of `f^*`.**
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal` is not an instance, so it is
introduced in each proof by hand, and with its *value* visible: the identification of its
cotensorator with `Stacks.RelativeVeryAmple.pullbackTensorModulesIso` holds by `rfl` and that is
unprovable once the structure has become an opaque hypothesis.

**The tensorator is not definitionally the inverse of the comparison of Tag 01CD.** It is
`CategoryTheory.inv` of its forward map, and `inv` is not an exposed definition under the module
system, so `(pullbackTensorModulesIso f A B).inv = μ f^* A B` is proved rather than taken by `rfl`
— from `CategoryTheory.Functor.Monoidal.δ_μ`, the cotensorator being the forward map by `rfl`.

**The degrees are spelled in several ways.** `((k + 1 : ℕ) : ℤ)` and `(k : ℤ) + 1` are equal and
not syntactically equal, and so are `Int.negSucc k` and `-((k + 1 : ℕ) : ℤ)`; `intIso_congr` and
`pullbackMul_of_eq` move between them, exactly as the transport leg's file does.

No Stacks registration is carried.  Tag 01CD is carried by `Stacks.RingedSpace.comparisonIso` and
Tag 01CU by the multiplication of the powers; this is a compatibility of the two, and the
natural-number half of it carries no attribute either.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory AlgebraicGeometry
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.AlgebraicGeometry.ThetaMul
open Stacks.AlgebraicGeometry.TensorPowCongrInt

namespace Stacks.TensorPowerPullbackMul

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

/-- **The multiplication transported through the tensorator of a monoidal functor is
associative**, when the multiplication it is transported from is, with every object free and a
transport of the total degree allowed on the right-hand side.

This is `Stacks.TensorPowerPullbackMul.laxMul_assoc` with its `ℕ`-indexed family of objects
removed: that statement writes the total degrees as `n + m` and `m + 1`, which an integer tridegree
cannot do — the associativity constraint
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int` carries a transport between the
two spellings `n + (m + c)` and `n + m + c` instead.  The proof is the same five rewrites: the
associativity coherence of the functor and the naturality of its tensorator in each variable, used
once each. -/
theorem laxMul_assoc_free {Pn Pm Pnm Pm1 Pnm1 Pnmc N : C}
    (anm : Pn ⊗ Pm ⟶ Pnm) (aLnm : Pnm ⊗ N ⟶ Pnmc) (aLm : Pm ⊗ N ⟶ Pm1)
    (anm1 : Pn ⊗ Pm1 ⟶ Pnm1) (tr : Pnm1 ⟶ Pnmc)
    (haL : anm ▷ N ≫ aLnm = (α_ Pn Pm N).hom ≫ Pn ◁ aLm ≫ anm1 ≫ tr) :
    (μ F Pn Pm ≫ F.map anm) ▷ F.obj N ≫ μ F Pnm N ≫ F.map aLnm =
      (α_ (F.obj Pn) (F.obj Pm) (F.obj N)).hom ≫
        F.obj Pn ◁ (μ F Pm N ≫ F.map aLm) ≫
          (μ F Pn Pm1 ≫ F.map anm1) ≫ F.map tr := by
  rw [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [μ_natural_left_assoc F anm N, ← F.map_comp, haL, F.map_comp, F.map_comp, F.map_comp,
    Functor.LaxMonoidal.associativity_assoc F Pn Pm N,
    ← μ_natural_right_assoc F Pn aLm]

/-- **The left unitor transported through the tensorator of a monoidal functor is a left
unitor**, the unit object being matched by the counit of the functor.  This is the left unit
coherence of the functor, and the mirror of `Stacks.TensorPowerPullbackMul.laxMul_unitor`: the
right-hand version is what a bidegree `(n, 0)` square needs and this one is what pins the degree
one value of a comparison family down. -/
theorem laxMul_unitor_left {N₀ : C} (u : N₀ ≅ 𝟙_ C) (A : C) :
    μ F N₀ A ≫ F.map (u.hom ▷ A ≫ (λ_ A).hom) =
      (F.map u.hom ≫ η F) ▷ F.obj A ≫ (λ_ (F.obj A)).hom := by
  rw [F.map_comp, ← μ_natural_left_assoc F u.hom A,
    Functor.LaxMonoidal.left_unitality F A, ← MonoidalCategory.comp_whiskerRight_assoc,
    Category.assoc, Functor.Monoidal.η_ε, Category.comp_id]

end Abstract

end Stacks.TensorPowerPullbackMul

namespace Stacks.AlgebraicGeometry.PullbackTensorPowInt

open Stacks.TensorPowerPullbackMul

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal
  Stacks.RelativeVeryAmple.ringSheafMonoidal

/-! ### Free-shape bookkeeping -/

/-- The inverse of an isomorphism is determined by a right inverse of its forward map.  Needed
because `CategoryTheory.inv` is not exposed under the module system, so the tensorator of `f^*` —
which is `inv` of the comparison of [Stacks, Tag 01CD] — is not definitionally the comparison's
`Iso.inv`. -/
private theorem iso_inv_eq_of_hom_comp {D : Type*} [Category D] {A B : D} (e : A ≅ B)
    {g : B ⟶ A} (h : e.hom ≫ g = CategoryStruct.id A) : e.inv = g := by
  rw [← Category.id_comp g, ← e.inv_hom_id, Category.assoc, h, Category.comp_id]

/-- **A tensor product of morphisms read out of a whiskering, with the second factor cancelled
against a retraction of it.**  The transport leg's `whisker_to_tensorHom` converts a whiskered
composite into a tensor product of morphisms; here the identity `negSucc_gate` provides carries the
*inverse* of the second factor on the other side of the square, so that factor has to be
cancelled as well.

Isolated with every object and morphism free: at the concrete objects the two spellings of the
degrees make a rewrite inside the composite fail to fire. -/
private theorem whisker_cancel_to_tensorHom {D : Type*} [Category D] [MonoidalCategory D]
    {A A' B E Y : D} (u : A ⟶ A') (g : E ⟶ B) (gi : B ⟶ E)
    (hg : g ≫ gi = CategoryStruct.id E) (rest : A' ⊗ B ⟶ Y) (mid : A ⊗ E ⟶ Y)
    (h : u ▷ B ≫ rest = A ◁ gi ≫ mid) : (u ⊗ₘ g) ≫ rest = mid := by
  rw [MonoidalCategory.tensorHom_def']
  simp only [Category.assoc]
  rw [h, ← MonoidalCategory.whiskerLeft_comp_assoc, hg, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- Cancelling an isomorphism on each side of an equation between two composites. -/
private theorem cancel_iso_both_free {D : Type*} [Category D] {A B E G : D} (u : A ≅ B)
    (x y : B ⟶ E) (v : E ≅ G) (h : u.hom ≫ x ≫ v.hom = u.hom ≫ y ≫ v.hom) : x = y :=
  (Iso.cancel_iso_hom_right x y v).mp
    ((Iso.cancel_iso_hom_left u (x ≫ v.hom) (y ≫ v.hom)).mp h)

/-- Splitting the last factor off a composite that a functor has been applied to: `w` is the
functor's image of a two-step composite and `t` the multiplication the first step produces.

Isolated with every object and morphism free because the concrete goals here are not type-correct
at the `implicit` transparency level — the two spellings of the structure ring sheaf of a scheme —
so `Category.assoc` cannot be used as a rewrite. -/
private theorem mu_map_comp_free {D : Type*} [Category D] {A B E G : D} (m : A ⟶ B) (u : B ⟶ E)
    (v : E ⟶ G) (w : B ⟶ G) (hw : w = u ≫ v) (t : A ⟶ E) (ht : t = m ≫ u) :
    m ≫ w = t ≫ v := by
  rw [hw, ht, Category.assoc]

/-- **The shape of the inverse-law identity `negSucc_gate` provides.**  Its right-hand side is a
five-fold composite whose middle factor is a functor applied to a three-fold composite, and the
bidegree square wants that factor split and the multiplication of the pulled-back powers read out
of the first two.  Free for the reason recorded in the implementation notes: at the concrete
objects neither `rw` nor `simp only` fires, the goal not being type-correct at the `implicit`
transparency level. -/
private theorem gate_shape_free {D : Type*} [Category D] {A B E G H K L : D}
    (p q : A ⟶ B) (d : B ⟶ E) (m : E ⟶ K) (m1 : E ⟶ G) (m2 : G ⟶ H) (m3 : H ⟶ K) (e : K ⟶ L)
    (hpq : p = q) (hm : m = m1 ≫ m2 ≫ m3) :
    p ≫ d ≫ m ≫ e = q ≫ (d ≫ m1) ≫ m2 ≫ m3 ≫ e := by
  rw [hpq, hm]
  simp only [Category.assoc]

/-! ### The multiplication of the pulled-back powers -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules) [IsInvertibleModule S M]

/-- **The multiplication of the pulled-back tensor powers**,
`f^*(M^{⊗ n}) ⊗ f^*(M^{⊗ m}) ≅ f^*(M^{⊗ (n+m)})`: the comparison of [Stacks, Tag 01CD] inverted,
followed by `f^*` applied to the addition law `Stacks.Ample.tensorPowModuleAddIso` of
[Stacks, Tag 01CU].  This is the multiplication that makes `⨁_{d ∈ ℤ} f^*(M^{⊗ d})` a graded
`𝒪_X`-algebra, and the one the comparison family has to carry to the addition law of the powers of
`f^*M`. -/
def pullbackPowMulIso (n m : ℤ) :
    (Scheme.Modules.pullback f).obj (tensorPowModule S M n) ⊗
        (Scheme.Modules.pullback f).obj (tensorPowModule S M m) ≅
      (Scheme.Modules.pullback f).obj (tensorPowModule S M (n + m)) :=
  (pullbackTensorModulesIso f (tensorPowModule S M n) (tensorPowModule S M m)).symm ≪≫
    (Scheme.Modules.pullback f).mapIso (tensorPowModuleAddIso S M n m)

/-- The forward map of the multiplication, unfolded. -/
theorem pullbackPowMulIso_hom (n m : ℤ) :
    (pullbackPowMulIso f M n m).hom =
      (pullbackTensorModulesIso f (tensorPowModule S M n) (tensorPowModule S M m)).inv ≫
        (Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M n m).hom :=
  rfl

/-- The multiplication of the pulled-back powers is the tensorator of `f^*` followed by `f^*` of the
addition law. -/
private theorem pullbackPowMulIso_hom_eq_mu (p q : ℤ) :
    letI : (Scheme.Modules.pullback f).Monoidal := pullbackComparisonMonoidal f.toLRSHom.toShHom
    (pullbackPowMulIso f M p q).hom =
      μ (Scheme.Modules.pullback f) (tensorPowModule S M p) (tensorPowModule S M q) ≫
        (Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M p q).hom := by
  let : (Scheme.Modules.pullback f).Monoidal := pullbackComparisonMonoidal f.toLRSHom.toShHom
  exact congrArg (fun z ↦ z ≫ (Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M p q).hom)
    (iso_inv_eq_of_hom_comp _
      (Functor.Monoidal.δ_μ (Scheme.Modules.pullback f) (tensorPowModule S M p)
        (tensorPowModule S M q)))

/-- **The pulled-back inverse law**, `f^*(M^{⊗ n}) ⊗ f^*(M^{⊗ (-n)}) ≅ 𝒪_X`: the multiplication at
the bidegree `(n, -n)`, reindexed to the degree zero where the power is the structure sheaf, and
followed by the structure-sheaf comparison of [Stacks, Tag 01CD].  This is the tensor inverse that
`Stacks.Monoidal.square_step_left` asks for of its third object. -/
def pullbackPowInvIso (n : ℤ) :
    (Scheme.Modules.pullback f).obj (tensorPowModule S M n) ⊗
        (Scheme.Modules.pullback f).obj (tensorPowModule S M (-n)) ≅ 𝟙_ X.Modules :=
  pullbackPowMulIso f M n (-n) ≪≫
    (Scheme.Modules.pullback f).mapIso
      (tensorPowModuleCongr S M (show n + -n = 0 from by ring) ≪≫ tensorPowModuleZeroIso S M) ≪≫
    Stacks.RelativeAmple.pullbackUnitModuleIso f

/-! ### The comparison family, degree by degree -/

/-- In a nonnegative degree the integer comparison is
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, by definition. -/
theorem intIso_natCast (k : ℕ) :
    pullbackTensorPowModuleIntIso f M ((k : ℕ) : ℤ) = pullbackTensorPowModuleIso f M k :=
  rfl

/-- **The degree zero value of the comparison**: `f^*𝒪_S ≅ 𝒪_X` read between the two zeroth
powers. -/
theorem intIso_zero_hom :
    (pullbackTensorPowModuleIntIso f M 0).hom =
      ((Scheme.Modules.pullback f).map (tensorPowModuleZeroIso S M).hom ≫
          (Stacks.RelativeAmple.pullbackUnitModuleIso f).hom) ≫
        (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).inv :=
  (Category.assoc _ _ _).symm

/-- **The comparison commutes with the reindexing along an equality of degrees.** -/
theorem intIso_congr {a b : ℤ} (h : b = a) :
    (pullbackTensorPowModuleIntIso f M b).hom =
      (Scheme.Modules.pullback f).map (tensorPowModuleCongr S M h).hom ≫
        (pullbackTensorPowModuleIntIso f M a).hom ≫
          (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M) h.symm).hom := by
  cases h
  rw [tensorPowModuleCongr_hom, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp,
    tensorPowModuleCongr_hom, eqToHom_refl, Category.comp_id]

/-- In a negative degree the integer comparison is `pullbackTensorPowModuleNegSuccIso`, the
comparison of two tensor inverses, with the two reindexings of `Int.negSucc k` as `-(k+1)`
cancelled. -/
theorem intIso_negSucc (k : ℕ) :
    (pullbackTensorPowModuleIntIso f M (-((k + 1 : ℕ) : ℤ))).hom =
      (pullbackTensorPowModuleNegSuccIso f M k).hom := by
  have hd : (Int.negSucc k) = -((k + 1 : ℕ) : ℤ) := by
    push_cast
    rfl
  have h1 : (pullbackTensorPowModuleIntIso f M (Int.negSucc k)).hom =
      (Scheme.Modules.pullback f).map (tensorPowModuleCongr S M hd).hom ≫
        (pullbackTensorPowModuleNegSuccIso f M k).hom ≫
          (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M) hd.symm).hom := rfl
  exact cancel_iso_both_free
    ((Scheme.Modules.pullback f).mapIso (tensorPowModuleCongr S M hd)) _ _
    (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M) hd.symm)
    ((intIso_congr f M hd).symm.trans h1)

/-! ### The associativity constraint of the pulled-back multiplication -/

/-- **Associativity of the multiplication of the pulled-back tensor powers, in an arbitrary
integer tridegree**, against the associator of the strict monoidal structure of [Stacks, Tag 01CA]
— the transport along `n + (m + c) = n + m + c` being the only reason the two targets are not
literally the same object.

This is `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int` on `S` pushed through
the monoidal functor `f^*` by `Stacks.TensorPowerPullbackMul.laxMul_assoc_free`. -/
theorem pullbackPowMulIso_assoc (n m c : ℤ) :
    (pullbackPowMulIso f M n m).hom ▷
          (Scheme.Modules.pullback f).obj (tensorPowModule S M c) ≫
        (pullbackPowMulIso f M (n + m) c).hom =
      (α_ ((Scheme.Modules.pullback f).obj (tensorPowModule S M n))
          ((Scheme.Modules.pullback f).obj (tensorPowModule S M m))
          ((Scheme.Modules.pullback f).obj (tensorPowModule S M c))).hom ≫
        (Scheme.Modules.pullback f).obj (tensorPowModule S M n) ◁
            (pullbackPowMulIso f M m c).hom ≫
          (pullbackPowMulIso f M n (m + c)).hom ≫
            (Scheme.Modules.pullback f).map
              (tensorPowModuleCongr S M (show n + (m + c) = n + m + c from by ring)).hom := by
  let : (Scheme.Modules.pullback f).Monoidal := pullbackComparisonMonoidal f.toLRSHom.toShHom
  simp only [pullbackPowMulIso_hom_eq_mu]
  exact laxMul_assoc_free (Scheme.Modules.pullback f) _ _ _ _ _
    (tensorPowModuleAddIso_assoc_int S M n m c)

/-! ### The squares -/

/-- **The multiplicativity square transported along equalities of the two degrees.** -/
theorem pullbackMul_of_eq {p q p' q' : ℤ} (hp : p = p') (hq : q = q')
    (H : (pullbackPowMulIso f M p q).hom ≫
          (pullbackTensorPowModuleIntIso f M (p + q)).hom =
        ((pullbackTensorPowModuleIntIso f M p).hom ⊗ₘ
            (pullbackTensorPowModuleIntIso f M q).hom) ≫
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) p q).hom) :
    (pullbackPowMulIso f M p' q').hom ≫
        (pullbackTensorPowModuleIntIso f M (p' + q')).hom =
      ((pullbackTensorPowModuleIntIso f M p').hom ⊗ₘ
          (pullbackTensorPowModuleIntIso f M q').hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) p' q').hom := by
  subst hp hq
  exact H

/-- **The right unit law of the multiplication of the pulled-back powers, in every integer
degree.**  This is `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_right_int` on `S`
pushed through `f^*` by `Stacks.TensorPowerPullbackMul.laxMul_unitor`. -/
theorem pullbackPowMulIso_zero_right (n : ℤ) :
    (Scheme.Modules.pullback f).obj (tensorPowModule S M n) ◁
          ((Scheme.Modules.pullback f).map (tensorPowModuleZeroIso S M).hom ≫
            (Stacks.RelativeAmple.pullbackUnitModuleIso f).hom) ≫
        (ρ_ ((Scheme.Modules.pullback f).obj (tensorPowModule S M n))).hom =
      (pullbackPowMulIso f M n 0).hom ≫
        (Scheme.Modules.pullback f).map
          (tensorPowModuleCongr S M (show n + 0 = n from by omega)).hom := by
  let : (Scheme.Modules.pullback f).Monoidal := pullbackComparisonMonoidal f.toLRSHom.toShHom
  exact (laxMul_unitor (Scheme.Modules.pullback f) (tensorPowModuleZeroIso S M)
      (tensorPowModule S M n)).symm.trans
    ((congrArg (fun z ↦ μ (Scheme.Modules.pullback f) (tensorPowModule S M n)
          (tensorPowModule S M 0) ≫ (Scheme.Modules.pullback f).map z)
        (tensorPowModuleAddIso_zero_right_int S M n)).trans
      (mu_map_comp_free _ _ _ _ ((Scheme.Modules.pullback f).map_comp _ _) _
        (pullbackPowMulIso_hom_eq_mu f M _ _)))

/-- **The left unit law of the multiplication of the pulled-back powers, in every integer
degree.**  This is `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left_int` on `S`
pushed through `f^*` by `Stacks.TensorPowerPullbackMul.laxMul_unitor_left`. -/
theorem pullbackPowMulIso_zero_left (c : ℤ) :
    ((Scheme.Modules.pullback f).map (tensorPowModuleZeroIso S M).hom ≫
            (Stacks.RelativeAmple.pullbackUnitModuleIso f).hom) ▷
          (Scheme.Modules.pullback f).obj (tensorPowModule S M c) ≫
        (λ_ ((Scheme.Modules.pullback f).obj (tensorPowModule S M c))).hom =
      (pullbackPowMulIso f M 0 c).hom ≫
        (Scheme.Modules.pullback f).map
          (tensorPowModuleCongr S M (show (0 : ℤ) + c = c from by omega)).hom := by
  let : (Scheme.Modules.pullback f).Monoidal := pullbackComparisonMonoidal f.toLRSHom.toShHom
  exact (laxMul_unitor_left (Scheme.Modules.pullback f) (tensorPowModuleZeroIso S M)
      (tensorPowModule S M c)).symm.trans
    ((congrArg (fun z ↦ μ (Scheme.Modules.pullback f) (tensorPowModule S M 0)
          (tensorPowModule S M c) ≫ (Scheme.Modules.pullback f).map z)
        (tensorPowModuleAddIso_zero_left_int S M c)).trans
      (mu_map_comp_free _ _ _ _ ((Scheme.Modules.pullback f).map_comp _ _) _
        (pullbackPowMulIso_hom_eq_mu f M _ _)))

/-- **Multiplicativity in the bidegree `(n, 0)`, for an arbitrary integer `n`.**  This is the
right unit law: both multiplications agree with the right unitor of [Stacks, Tag 01CA] on the
identification of the zeroth power with the structure sheaf, and the degree zero value of the
comparison *is* the pair of those identifications.  Nothing is needed about the value in the degree
`n`, which is why no sign condition appears. -/
theorem pullbackMul_zero (n : ℤ) :
    (pullbackPowMulIso f M n 0).hom ≫
        (pullbackTensorPowModuleIntIso f M (n + 0)).hom =
      ((pullbackTensorPowModuleIntIso f M n).hom ⊗ₘ
          (pullbackTensorPowModuleIntIso f M 0).hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) n 0).hom := by
  rw [intIso_congr f M (show n + 0 = n from by omega), intIso_zero_hom]
  exact zero_right_free (pullbackTensorPowModuleIntIso f M n).hom
    ((Scheme.Modules.pullback f).map (tensorPowModuleZeroIso S M).hom ≫
      (Stacks.RelativeAmple.pullbackUnitModuleIso f).hom)
    (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).inv
    (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).hom
    (pullbackPowMulIso f M n 0).hom
    ((Scheme.Modules.pullback f).map
      (tensorPowModuleCongr S M (show n + 0 = n from by omega)).hom)
    (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) n 0).hom
    (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
      (show n + 0 = n from by omega)).hom
    (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
      (show n = n + 0 from by omega)).hom
    (pullbackPowMulIso_zero_right f M n)
    (tensorPowModuleAddIso_zero_right_int X ((Scheme.Modules.pullback f).obj M) n)
    (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).inv_hom_id
    (tensorPowModuleCongr_comp X ((Scheme.Modules.pullback f).obj M) _ _)

/-- **Multiplicativity in a bidegree of natural numbers**, at the integer spelling of the two
exponents.  This is
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso` retyped: in a
nonnegative degree the integer comparison is the natural-number one by definition, and the two
multiplications differ only by whether the comparison of [Stacks, Tag 01CD] stands at the head of
the composite or has been inverted into the multiplication. -/
theorem pullbackMul_natCast (a b : ℕ) :
    (pullbackPowMulIso f M (a : ℤ) (b : ℤ)).hom ≫
        (pullbackTensorPowModuleIntIso f M ((a : ℤ) + (b : ℤ))).hom =
      ((pullbackTensorPowModuleIntIso f M (a : ℤ)).hom ⊗ₘ
          (pullbackTensorPowModuleIntIso f M (b : ℤ)).hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) (a : ℤ) (b : ℤ)).hom :=
  (Category.assoc
      (pullbackTensorModulesIso f (tensorPowModule S M (a : ℤ))
        (tensorPowModule S M (b : ℤ))).inv
      ((Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M (a : ℤ) (b : ℤ)).hom)
      (pullbackTensorPowModuleIntIso f M ((a : ℤ) + (b : ℤ))).hom).trans
    (comp_eq_of_eq_comp _ _ (Iso.inv_hom_id _)
      (pullbackTensorPowModuleIso_tensorPowModuleAddIso f M a b))

/-- **The bidegree `(n, 1)` column at a natural number `n`, with the recursion's own second
factor.**  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` is defined by a recursion whose
step splits the `(n+1)`-st power as `M^{⊗ n} ⊗ M^{⊗ 1}`, applies the comparison of
[Stacks, Tag 01CD], and compares the second factor by
`Stacks.RelativeVeryAmple.pullbackPowOneIso`; this is
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_succ_square` retyped.

It is the column the chase needs, except that the second factor is the recursion's rather than the
degree one value of the family itself; the two are identified by `intIso_one_eq`, which is this
statement at `n = 0`. -/
theorem pullbackMul_one_natCast_aux (k : ℕ) :
    (pullbackPowMulIso f M (k : ℤ) 1).hom ≫
        (pullbackTensorPowModuleIntIso f M ((k : ℤ) + 1)).hom =
      ((pullbackTensorPowModuleIntIso f M (k : ℤ)).hom ⊗ₘ (pullbackPowOneIso f M).hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) (k : ℤ) 1).hom :=
  (Category.assoc
      (pullbackTensorModulesIso f (tensorPowModule S M (k : ℤ)) (tensorPowModule S M 1)).inv
      ((Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M (k : ℤ) 1).hom)
      (pullbackTensorPowModuleIntIso f M ((k : ℤ) + 1)).hom).trans
    (comp_eq_of_eq_comp _ _ (Iso.inv_hom_id _)
      (pullbackTensorPowModuleIso_succ_square f M k))

/-- **The degree one value of the comparison family** is
`Stacks.RelativeVeryAmple.pullbackPowOneIso`, `f^*(M^{⊗ 1}) ≅ f^*M ≅ (f^*M)^{⊗ 1}`.

The recursion defining `pullbackTensorPowModuleIso` produces, in the degree one, the comparison in
the degree zero on a first factor `f^*(M^{⊗ 0})` that is still present; this reads it off, the
identification being the two left unit laws `pullbackPowMulIso_zero_left` and
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left_int`. -/
theorem intIso_one_eq :
    (pullbackTensorPowModuleIntIso f M 1).hom = (pullbackPowOneIso f M).hom := by
  have hcol := pullbackMul_one_natCast_aux f M 0
  rw [show (((0 : ℕ) : ℤ)) = (0 : ℤ) from by omega] at hcol
  rw [intIso_zero_hom, intIso_congr f M (show (0 : ℤ) + 1 = 1 from by omega)] at hcol
  exact one_eq_free
    ((Scheme.Modules.pullback f).map (tensorPowModuleZeroIso S M).hom ≫
      (Stacks.RelativeAmple.pullbackUnitModuleIso f).hom)
    (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).inv
    (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).hom
    (pullbackPowOneIso f M).hom
    (pullbackTensorPowModuleIntIso f M 1).hom
    (pullbackPowMulIso f M 0 1).hom
    ((Scheme.Modules.pullback f).map
      (tensorPowModuleCongr S M (show (0 : ℤ) + 1 = 1 from by omega)).hom)
    (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) 0 1).hom
    (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
      (show (0 : ℤ) + 1 = 1 from by omega)).hom
    (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
      (show (1 : ℤ) = 0 + 1 from by omega)).hom
    (pullbackPowMulIso_zero_left f M 1)
    (tensorPowModuleAddIso_zero_left_int X ((Scheme.Modules.pullback f).obj M) 1)
    (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).inv_hom_id
    (tensorPowModuleCongr_comp X ((Scheme.Modules.pullback f).obj M) _ _)
    (pullbackPowMulIso f M 0 1 ≪≫
      (Scheme.Modules.pullback f).mapIso
        (tensorPowModuleCongr S M (show (0 : ℤ) + 1 = 1 from by omega))) rfl
    hcol

/-- **The bidegree `(n, 1)` column at a natural number `n`**, with the degree one value of the
family itself on the second factor. -/
theorem pullbackMul_one_natCast (k : ℕ) :
    (pullbackPowMulIso f M (k : ℤ) 1).hom ≫
        (pullbackTensorPowModuleIntIso f M ((k : ℤ) + 1)).hom =
      ((pullbackTensorPowModuleIntIso f M (k : ℤ)).hom ⊗ₘ
          (pullbackTensorPowModuleIntIso f M 1).hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) (k : ℤ) 1).hom := by
  rw [intIso_one_eq]
  exact pullbackMul_one_natCast_aux f M k

/-- **The multiplicativity square in the bidegree `(p, b + c)`, read at the `(A, BC)` corner of the
associativity diagram in the tridegree `(p, b, c)`.**  The two sides differ only by where the
transport between the two spellings `p + (b + c)` and `p + b + c` of the total degree sits.  The
second form is what `Stacks.AlgebraicGeometry.ThetaMul.square_step` produces and what
`Stacks.Monoidal.square_step_left` consumes, because the associativity constraints of both
families carry that transport. -/
theorem pullbackMul_corner_iff (p b c : ℤ) :
    ((pullbackPowMulIso f M p (b + c)).hom ≫
          (pullbackTensorPowModuleIntIso f M (p + (b + c))).hom =
        ((pullbackTensorPowModuleIntIso f M p).hom ⊗ₘ
            (pullbackTensorPowModuleIntIso f M (b + c)).hom) ≫
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) p (b + c)).hom) ↔
      (((pullbackPowMulIso f M p (b + c)).hom ≫
              (Scheme.Modules.pullback f).map (tensorPowModuleCongr S M
                (show p + (b + c) = p + b + c from by ring)).hom) ≫
            (pullbackTensorPowModuleIntIso f M (p + b + c)).hom =
        ((pullbackTensorPowModuleIntIso f M p).hom ⊗ₘ
            (pullbackTensorPowModuleIntIso f M (b + c)).hom) ≫
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) p (b + c)).hom ≫
            (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
              (show p + (b + c) = p + b + c from by ring)).hom) :=
  Iff.trans
    (Iff.of_eq (congrArg (fun z ↦ z = ((pullbackTensorPowModuleIntIso f M p).hom ⊗ₘ
        (pullbackTensorPowModuleIntIso f M (b + c)).hom) ≫
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) p (b + c)).hom)
      (congrArg (fun z ↦ (pullbackPowMulIso f M p (b + c)).hom ≫ z)
        (intIso_congr f M (show p + (b + c) = p + b + c from by ring)))))
    (Stacks.AlgebraicGeometry.ThetaMul.absorb_iff _ _ _ _ _ _ _
      (tensorPowModuleCongr_comp X ((Scheme.Modules.pullback f).obj M) _ _)
      (tensorPowModuleCongr_comp X ((Scheme.Modules.pullback f).obj M) _ _))

/-- **The characterising identity of the comparison in a negative degree.**
`pullbackTensorPowModuleNegSuccIso` is
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso` of the two inverse laws of
`(f^*M)^{⊗ (k+1)}` carried by `f^*(M^{⊗ -(k+1)})` and by `(f^*M)^{⊗ -(k+1)}`, and
`Stacks.AlgebraicGeometry.TensorUnitInvLaw.isoOfTensorUnitIso_whiskerRight` says it carries the
second law back to the first. -/
private theorem negSucc_gate (k : ℕ) :
    (pullbackTensorPowModuleNegSuccIso f M k).hom ▷
          tensorPowModule X ((Scheme.Modules.pullback f).obj M) ((k + 1 : ℕ) : ℤ) ≫
        ((tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M)
              (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
          (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
            (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring)).hom ≫
          (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).hom) =
      (tensorModulesMapIso X (Iso.refl _) (pullbackTensorPowModuleIso f M (k + 1)).symm ≪≫
        (pullbackTensorModulesIso f (tensorPowModule S M (-((k + 1 : ℕ) : ℤ)))
          (tensorPowModule S M ((k + 1 : ℕ) : ℤ))).symm ≪≫
        (Scheme.Modules.pullback f).mapIso
          (tensorPowModuleAddIso S M (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) ≪≫
            tensorPowModuleCongr S M
              (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring) ≪≫
            tensorPowModuleZeroIso S M) ≪≫
        Stacks.RelativeAmple.pullbackUnitModuleIso f).hom :=
  Stacks.AlgebraicGeometry.TensorUnitInvLaw.isoOfTensorUnitIso_whiskerRight X _ _ _ _ _

/-- **The inverse-law square for the pullback comparison**, in the bidegree `(-(k+1), k+1)`: the
comparisons in the two degrees, tensored together, carry the pulled-back inverse law of the powers
of `M` to the inverse law of the powers of `f^*M`.  This is the one face of the multiplicativity
statement that no arrangement of `Stacks.AlgebraicGeometry.ThetaMul.square_step` and
`Stacks.Monoidal.square_step_left` reaches from the nonnegative degrees. -/
theorem pullbackMul_neg_succ (k : ℕ) :
    (pullbackPowMulIso f M (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
        (pullbackTensorPowModuleIntIso f M
          (-((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ))).hom =
      ((pullbackTensorPowModuleIntIso f M (-((k + 1 : ℕ) : ℤ))).hom ⊗ₘ
          (pullbackTensorPowModuleIntIso f M ((k + 1 : ℕ) : ℤ)).hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M)
          (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom := by
  have hgate : ((pullbackTensorPowModuleIntIso f M (-((k + 1 : ℕ) : ℤ))).hom ⊗ₘ
        (pullbackTensorPowModuleIntIso f M ((k + 1 : ℕ) : ℤ)).hom) ≫
      ((tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M)
            (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
        (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
          (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring)).hom ≫
        (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).hom) =
      (pullbackPowMulIso f M (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫
        (Scheme.Modules.pullback f).map
            (tensorPowModuleCongr S M
              (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring)).hom ≫
          ((Scheme.Modules.pullback f).map (tensorPowModuleZeroIso S M).hom ≫
            (Stacks.RelativeAmple.pullbackUnitModuleIso f).hom) := by
    rw [intIso_negSucc, intIso_natCast]
    refine whisker_cancel_to_tensorHom _ _ (pullbackTensorPowModuleIso f M (k + 1)).inv
      (pullbackTensorPowModuleIso f M (k + 1)).hom_inv_id _ _ ?_
    refine (negSucc_gate f M k).trans ?_
    exact gate_shape_free _ _ _ _
      ((Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M
        (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom) _ _ _
      ((Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom X (Iso.refl _)
          (pullbackTensorPowModuleIso f M (k + 1)).symm).trans
        (MonoidalCategory.id_tensorHom _ _))
      (((Scheme.Modules.pullback f).map_comp _ _).trans
        (congrArg (fun z ↦ (Scheme.Modules.pullback f).map
            (tensorPowModuleAddIso S M (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ)).hom ≫ z)
          ((Scheme.Modules.pullback f).map_comp _ _)))
  rw [intIso_congr f M (show -((k + 1 : ℕ) : ℤ) + ((k + 1 : ℕ) : ℤ) = 0 from by ring),
    intIso_zero_hom]
  exact inv_law_square_free _ _ _ _ _ _ _ _ _ hgate
    (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).hom_inv_id
    (tensorPowModuleCongr_comp X ((Scheme.Modules.pullback f).obj M) _ _)

/-- **The inverse-law square at every bidegree summing to zero with a nonnegative second
exponent.**  In the degree zero it is the right unit law `pullbackMul_zero`, and otherwise it is
`pullbackMul_neg_succ`. -/
theorem pullbackMul_add_eq_zero (p q : ℤ) (hq : 0 ≤ q) (hpq : p + q = 0) :
    (pullbackPowMulIso f M p q).hom ≫
        (pullbackTensorPowModuleIntIso f M (p + q)).hom =
      ((pullbackTensorPowModuleIntIso f M p).hom ⊗ₘ
          (pullbackTensorPowModuleIntIso f M q).hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) p q).hom := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  cases j with
  | zero =>
      exact pullbackMul_of_eq f M (show (0 : ℤ) = p from by omega)
        (show (0 : ℤ) = ((0 : ℕ) : ℤ) from by omega) (pullbackMul_zero f M 0)
  | succ i =>
      exact pullbackMul_of_eq f M (show -(((i + 1 : ℕ)) : ℤ) = p from by omega) rfl
        (pullbackMul_neg_succ f M i)

/-- **Multiplicativity in the bidegree `(k, 1)` for an arbitrary integer `k`.**  In a nonnegative
degree this is `pullbackMul_one_natCast`.  In a negative degree `k = -(a+1)` it is
`Stacks.Monoidal.square_step_left` applied to the associativity diagram in the tridegree
`(-(a+1), 1, a)`, whose other three squares are the two inverse-law squares at `(-a, a)` and at
`(-(a+1), a+1)` and the natural-number square at `(1, a)`. -/
theorem pullbackMul_one (k : ℤ) :
    (pullbackPowMulIso f M k 1).hom ≫
        (pullbackTensorPowModuleIntIso f M (k + 1)).hom =
      ((pullbackTensorPowModuleIntIso f M k).hom ⊗ₘ
          (pullbackTensorPowModuleIntIso f M 1).hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) k 1).hom := by
  by_cases hk : 0 ≤ k
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact pullbackMul_one_natCast f M j
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, k = -((a : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    exact Stacks.Monoidal.square_step_left_of_mono
      (Stacks.Monoidal.mono_iso_hom
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M)
          (-((a : ℤ) + 1) + 1) (a : ℤ)))
      (pullbackPowInvIso f M (a : ℤ))
      (pullbackPowMulIso_assoc f M (-((a : ℤ) + 1)) 1 (a : ℤ))
      (tensorPowModuleAddIso_assoc_int X ((Scheme.Modules.pullback f).obj M)
        (-((a : ℤ) + 1)) 1 (a : ℤ))
      (pullbackMul_add_eq_zero f M (-((a : ℤ) + 1) + 1) (a : ℤ) (by omega) (by ring))
      (pullbackMul_of_eq f M (show (((1 : ℕ)) : ℤ) = 1 from by omega) rfl
        (pullbackMul_natCast f M 1 a))
      ((pullbackMul_corner_iff f M (-((a : ℤ) + 1)) 1 (a : ℤ)).mp
        (pullbackMul_add_eq_zero f M (-((a : ℤ) + 1)) (1 + (a : ℤ)) (by omega) (by ring)))

/-- **Multiplicativity of the comparison `f^*(M^{⊗ d}) ≅ (f^*M)^{⊗ d}` in an arbitrary integer
bidegree**: the multiplication `pullbackPowMulIso` of the pulled-back powers at `(n, m)`, followed
by the comparison in the degree `n + m`, is the comparisons in the degrees `n` and `m` on the two
factors, followed by the addition law `Stacks.Ample.tensorPowModuleAddIso` of the powers of `f^*M`.
Both degrees are arbitrary integers.

This is the statement that makes
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso` an isomorphism of
`ℤ`-graded `𝒪_X`-algebras rather than a degreewise family of isomorphisms.

The induction is over `ℤ` in the second degree, with the bidegree `(n, 0)` square as base case,
`Stacks.AlgebraicGeometry.ThetaMul.square_step` upwards and
`Stacks.Monoidal.square_step_left_of_mono` downwards, both fed with the two associativity
constraints `pullbackPowMulIso_assoc` and
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int` in the tridegree `(n, m, 1)`
and with the bidegree `(k, 1)` column `pullbackMul_one`. -/
theorem pullbackTensorPowModuleIntIso_mul (n m : ℤ) :
    (pullbackPowMulIso f M n m).hom ≫
        (pullbackTensorPowModuleIntIso f M (n + m)).hom =
      ((pullbackTensorPowModuleIntIso f M n).hom ⊗ₘ
          (pullbackTensorPowModuleIntIso f M m).hom) ≫
        (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) n m).hom := by
  induction m using Int.induction_on with
  | zero => exact pullbackMul_zero f M n
  | succ i ih =>
      exact (pullbackMul_corner_iff f M n (i : ℤ) 1).mpr
        (Stacks.AlgebraicGeometry.ThetaMul.square_step
          (pullbackPowMulIso_assoc f M n (i : ℤ) 1)
          (tensorPowModuleAddIso_assoc_int X ((Scheme.Modules.pullback f).obj M) n (i : ℤ) 1)
          ih (pullbackMul_one f M (n + (i : ℤ))) (pullbackMul_one f M (i : ℤ)))
  | pred i ih =>
      exact Stacks.Monoidal.square_step_left_of_mono
        (Stacks.Monoidal.mono_iso_hom
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M)
            (n + (-(i : ℤ) - 1)) 1))
        (pullbackPowInvIso f M 1)
        (pullbackPowMulIso_assoc f M n (-(i : ℤ) - 1) 1)
        (tensorPowModuleAddIso_assoc_int X ((Scheme.Modules.pullback f).obj M)
          n (-(i : ℤ) - 1) 1)
        (pullbackMul_one f M (n + (-(i : ℤ) - 1)))
        (pullbackMul_one f M (-(i : ℤ) - 1))
        ((pullbackMul_corner_iff f M n (-(i : ℤ) - 1) 1).mp
          (pullbackMul_of_eq f M rfl (show -(i : ℤ) = -(i : ℤ) - 1 + 1 from by omega) ih))

/-- **The same square, written exactly as the natural-number statement is written.** The
multiplication of the pulled-back powers has the comparison of [Stacks, Tag 01CD] at the head of
the composite rather than inverted into it, so this is
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso` with the restriction to
nonnegative degrees removed, and the two are visibly the same statement. -/
theorem pullbackTensorPowModuleIntIso_tensorPowModuleAddIso (n m : ℤ) :
    (Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M n m).hom ≫
        (pullbackTensorPowModuleIntIso f M (n + m)).hom =
      (pullbackTensorModulesIso f (tensorPowModule S M n) (tensorPowModule S M m)).hom ≫
        ((pullbackTensorPowModuleIntIso f M n).hom ⊗ₘ
            (pullbackTensorPowModuleIntIso f M m).hom) ≫
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) n m).hom :=
  eq_comp_of_comp_eq _ _ (Iso.hom_inv_id _) (pullbackTensorPowModuleIntIso_mul f M n m)

end Stacks.AlgebraicGeometry.PullbackTensorPowInt

end
