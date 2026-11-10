module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensor

/-!
# The unit isomorphism of the relative tensor product of graded modules

Let `O` be a sheaf of commutative rings on a site and let `A` be a sheaf of graded `O`-algebras.
Regarding `A` as a right graded module over itself, the relative tensor product `A ⊗_A N` with a
left graded `A`-module `N` is `N`: this file constructs that isomorphism, degree by degree, and
draws the consequence that `A` is flat as a right graded module over itself.

## Main definitions

* `SheafOfModules.GradedModule.regularModule` regards a sheaf of graded algebras as a right
  graded module over itself.
* `SheafOfModules.RelativeTensor.unitorBalanced` is the balanced bilinear family `(a, y) ↦ ay`,
  and `SheafOfModules.RelativeTensor.unitorHom` is the morphism `A ⊗_A N → N` it descends to.
* `SheafOfModules.RelativeTensor.oneTmul` is the morphism `y ↦ 1 ⊗ y` into the summand
  `A^0 ⊗_O N^n`, and `SheafOfModules.RelativeTensor.unitorInv` is the morphism
  `N → A ⊗_A N` it induces.
* `SheafOfModules.RelativeTensor.unitorIso` is **the unit isomorphism** `A ⊗_A N ≅ N` in
  degree `n`.

## Main results

* `SheafOfModules.RelativeTensor.unitorHom_tmul` computes the unitor on a local section
  `a ⊗ y`: it is `ay`, transported along the equality of degrees.
* `SheafOfModules.RelativeTensor.unitorHom_naturality`: the unitor is natural in the left graded
  module.
* `SheafOfModules.RelativeTensor.isGradedFlat_regularModule`: a sheaf of graded algebras is flat
  as a right graded module over itself, since `N ↦ A ⊗_A N` is isomorphic to the identity.

## Implementation notes

The unitor is stated degreewise, as an isomorphism `A ⊗_A N ≅ N` of sheaves of modules in each
degree `n` rather than as a single isomorphism in a category of graded modules. This is forced by
the construction: `SheafOfModules.RelativeTensor.gradedTensor` produces one sheaf of modules per
degree and there is no category of graded modules over `A` in which `A ⊗_A N` is an object — the
functor `SheafOfModules.RelativeTensor.gradedTensorFunctor` lands in `GradedObject ℤ` of sheaves
of modules, not in left graded modules, because the left action on `P ⊗_A N` is not part of this
development.

The cast burden of a degreewise statement is confined to one place. A balanced bilinear family of
total degree `n` must take values in a single sheaf of modules, while `ay` lives in degree
`p + q` for `a` of degree `p` and `y` of degree `q`; the two agree only propositionally. So
`SheafOfModules.RelativeTensor.unitorBilinear` transports the action along the defining equality
of a `SheafOfModules.TensorIndex`, and
`SheafOfModules.RelativeTensor.unitorBilinear_app` removes the transport by substituting that
equality. Every later proof destructures the index and substitutes, after which no cast remains;
the three lemmas of the `GradedCast` section below are what make the substituted form meet the
`HEq`s in which `SheafOfModules.LeftGradedModule` records associativity and unitality.

## References

* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t m v u

namespace SheafOfModules

section GradedCast

variable {ι : Type*} {Y : ι → Type*}

/-- A transport along an equality of indices is determined by a heterogeneous equality. -/
theorem gradedCast_eq_of_heq {i j : ι} (h : i = j) {y : Y i} {z : Y j} (e : HEq y z) :
    gradedCast Y h y = z := by
  subst h
  exact eq_of_heq e

/-- The mirror of `SheafOfModules.gradedCast_eq_of_heq`, with the transport on the right. -/
theorem eq_gradedCast_of_heq {i j : ι} (h : j = i) {y : Y i} {z : Y j} (e : HEq y z) :
    y = gradedCast Y h z := by
  subst h
  exact eq_of_heq e

/-- Two transports into one and the same index agree on heterogeneously equal terms. -/
theorem gradedCast_eq_gradedCast {i j k : ι} (h₁ : i = k) (h₂ : j = k) {y : Y i} {z : Y j}
    (e : HEq y z) : gradedCast Y h₁ y = gradedCast Y h₂ z := by
  subst h₁
  subst h₂
  exact eq_of_heq e

/-- A transport commutes with a family of maps indexed by the same index type. -/
theorem gradedCast_dependent {Z : ι → Type*} (g : ∀ k, Y k → Z k) {i j : ι} (h : i = j)
    (y : Y i) : g j (gradedCast Y h y) = gradedCast Z h (g i y) := by
  subst h
  rfl

end GradedCast

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace GradedModule

/-- A sheaf of graded algebras, acting on itself on the right. This is the graded counterpart of
`SheafOfModules.DifferentialGradedModule.regularModule`. -/
@[stacks 0FQZ "a sheaf of graded algebras as a right graded module over itself"]
def regularModule (A : GradedAlgebra.{t, m} R) : GradedModule.{t, m, m} A where
  piece := A.piece
  smul n i U := (A.mul n i).app U
  smul_smul_left n i U r x y := (A.mul n i).map_smul_left U r x y
  smul_smul_right n i U r x y := (A.mul n i).map_smul_right U r x y
  smul_naturality n i _U _V f x y := (A.mul n i).naturality f x y
  smul_mul n i j U x y z := A.mul_assoc n i j U x y z
  smul_one n U x := A.mul_one n U x

/-- The piece of degree `n` of the regular module of `A` is the piece of degree `n` of `A`. -/
@[simp]
theorem regularModule_piece (A : GradedAlgebra.{t, m} R) (n : ℤ) :
    (regularModule A).piece n = A.piece n := rfl

/-- The action of the regular module of `A` is the multiplication of `A`. -/
@[simp]
theorem regularModule_smul (A : GradedAlgebra.{t, m} R) (n i : ℤ) (U : Cᵒᵖ) :
    (regularModule A).smul n i U = (A.mul n i).app U := rfl

end GradedModule

variable [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}} {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}

namespace RelativeTensor

/-! ### A local section transported in the left degree -/

variable (P : GradedModule.{t, m, m} A) (N : LeftGradedModule.{t, m, m} A)

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- The local section `x ⊗ y` of `P ⊗_A N` is unchanged when the degree of `x` is transported
along an equality of integers. This is the `SheafOfModules.RelativeTensor.tmul` counterpart of
`SheafOfModules.RelativeTensor.tensorSumι_cast_left`. -/
theorem tmul_cast_left {p p' q n : ℤ} (hp : p = p') (h : p + q = n) (X : Cᵒᵖ)
    (x : (P.piece p).val.obj X) (y : (N.piece q).val.obj X) :
    tmul P N n (⟨(p', q), by rw [← hp]; exact h⟩ : TensorIndex n) X
        (gradedCast (fun k ↦ (P.piece k).val.obj X) hp x) y =
      tmul P N n (⟨(p, q), h⟩ : TensorIndex n) X x y := by
  subst hp
  rfl

/-- The local section `x ⊗ y` of `P ⊗_A N` is unchanged when the degree of `y` is transported
along an equality of integers. This is the `SheafOfModules.RelativeTensor.tmul` counterpart of
`SheafOfModules.RelativeTensor.tensorSumι_cast_right`. -/
theorem tmul_cast_right {p q q' n : ℤ} (hq : q = q') (h : p + q = n) (X : Cᵒᵖ)
    (x : (P.piece p).val.obj X) (y : (N.piece q).val.obj X) :
    tmul P N n (⟨(p, q'), by rw [← hq]; exact h⟩ : TensorIndex n) X x
        (gradedCast (fun k ↦ (N.piece k).val.obj X) hq y) =
      tmul P N n (⟨(p, q), h⟩ : TensorIndex n) X x y := by
  subst hq
  rfl

end Sheafify

/-! ### The balanced bilinear family `(a, y) ↦ ay` -/

/-- The action of `A` on `N` as a bilinear family of total degree `n`: it sends `(a, y)` to
`ay`, transported along the equality `p + q = n` of degrees. -/
noncomputable def unitorBilinear {p q n : ℤ} (h : p + q = n) :
    Stacks.BilinearMap (A.piece p).val (N.piece q).val (N.piece n).val :=
  h ▸ PresheafOfModules.toBilinear (N.smulHom p q)

/-- On local sections, `SheafOfModules.RelativeTensor.unitorBilinear` sends `(a, y)` to `ay`,
transported along the equality `p + q = n`. -/
@[simp]
theorem unitorBilinear_app {p q n : ℤ} (h : p + q = n) (X : Cᵒᵖ)
    (a : (A.piece p).val.obj X) (y : (N.piece q).val.obj X) :
    (unitorBilinear N h).app X a y =
      gradedCast (fun k ↦ (N.piece k).val.obj X) h (N.smul p q X a y) := by
  subst h
  exact N.smulHom_tmul p q X a y

/-- **The action of `A` on `N` is balanced.** This is associativity of the action together with
associativity of the multiplication of `A`, the latter being the right action of `A` on itself. -/
noncomputable def unitorBalanced (n : ℤ) :
    Balanced (GradedModule.regularModule A) N (N.piece n).val n where
  app p := unitorBilinear N p.2
  balanced i X x a y :=
    ((unitorBilinear_app N (leftIndex i).2 X _ y).trans
      (gradedCast_eq_gradedCast (Y := fun k ↦ (N.piece k).val.obj X) (leftIndex i).2
        (rightIndex i).2 (N.mul_smul i.1.1 i.1.2.1 i.1.2.2 X x a y))).trans
      (unitorBilinear_app N (rightIndex i).2 X x _).symm

/-! ### The morphism `y ↦ 1 ⊗ y` -/

/-- The morphism `y ↦ 1 ⊗ y` from degree `n` of `N` into the summand `A^0 ⊗_O N^n` of the direct
sum computing degree `n` of `A ⊗_A N`. -/
noncomputable def oneTmul (n : ℤ) :
    (N.piece n).val ⟶ PresheafOfModules.tensorObj (A.piece 0).val (N.piece n).val where
  app X := ModuleCat.ofHom
    { toFun := fun y ↦ A.one.eval X ⊗ₜ y
      map_add' := fun y y' ↦ TensorProduct.tmul_add _ y y'
      map_smul' := fun r y ↦ TensorProduct.tmul_smul r _ y }
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    change A.one.eval Y ⊗ₜ[((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj Y : RingCat)]
        ((N.piece n).val.restrictₛₗ f y) =
      (PresheafOfModules.tensorObj (A.piece 0).val (N.piece n).val).restrictₛₗ f
        (A.one.eval X ⊗ₜ[((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj X : RingCat)] y)
    rw [PresheafOfModules.tensorObj_restrictₛₗ_tmul]
    exact congrArg (fun z ↦ z ⊗ₜ[((Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj Y : RingCat)]
      (N.piece n).val.restrictₛₗ f y) (PresheafOfModules.sections_property A.one f).symm

/-- On local sections, `SheafOfModules.RelativeTensor.oneTmul` sends `y` to `1 ⊗ y`. -/
@[simp]
theorem oneTmul_app (n : ℤ) (X : Cᵒᵖ) (y : (N.piece n).val.obj X) :
    PresheafOfModules.Hom.app (oneTmul N n) X y = A.one.eval X ⊗ₜ y := rfl

/-! ### The unit isomorphism -/

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- **The unitor of `A ⊗_A N`**: the morphism `A ⊗_A N → N` in degree `n` which sends a local
section `a ⊗ y` to `ay`. -/
noncomputable def unitorHom (n : ℤ) :
    gradedTensor (GradedModule.regularModule A) N n ⟶ N.piece n :=
  (unitorBalanced N n).desc (GradedModule.regularModule A) N

/-- The unitor sends a local section `a ⊗ y` to `ay`, transported along the equality of degrees.
-/
theorem unitorHom_tmul (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (a : (A.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (unitorHom N n).val X
        (tmul (GradedModule.regularModule A) N n p X a y) =
      gradedCast (fun k ↦ (N.piece k).val.obj X) p.2 (N.smul p.1.1 p.1.2 X a y) :=
  ((unitorBalanced N n).desc_tmul (GradedModule.regularModule A) N p X a y).trans
    (unitorBilinear_app N p.2 X a y)

/-- **The inverse of the unitor of `A ⊗_A N`**: the morphism `N → A ⊗_A N` in degree `n` which
sends a local section `y` to `1 ⊗ y`. -/
noncomputable def unitorInv (n : ℤ) :
    N.piece n ⟶ gradedTensor (GradedModule.regularModule A) N n :=
  ⟨oneTmul N n ≫ tensorSumι (GradedModule.regularModule A) N
      (⟨(0, n), zero_add n⟩ : TensorIndex n) ≫
    gradedTensorπ (GradedModule.regularModule A) N n ≫
      gradedTensorUnit (GradedModule.regularModule A) N n⟩

/-- The inverse of the unitor sends a local section `y` to `1 ⊗ y`. -/
theorem unitorInv_apply (n : ℤ) (X : Cᵒᵖ) (y : (N.piece n).val.obj X) :
    PresheafOfModules.Hom.app (unitorInv N n).val X y =
      tmul (GradedModule.regularModule A) N n (⟨(0, n), zero_add n⟩ : TensorIndex n) X
        (A.one.eval X) y := rfl

/-- The composite `N → A ⊗_A N → N` is the identity: this is unitality of the action. -/
theorem unitorInv_comp_unitorHom (n : ℤ) :
    unitorInv N n ≫ unitorHom N n = 𝟙 (N.piece n) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
  change PresheafOfModules.Hom.app (unitorHom N n).val X
      (PresheafOfModules.Hom.app (unitorInv N n).val X y) = y
  rw [unitorInv_apply, unitorHom_tmul]
  exact gradedCast_eq_of_heq (zero_add n) (N.one_smul n X y)

/-- The composite `A ⊗_A N → N → A ⊗_A N` is the identity: on a local section `a ⊗ y` this is
the balancing relation `1a ⊗ y = 1 ⊗ ay` together with unitality of the multiplication. -/
theorem unitorHom_comp_unitorInv (n : ℤ) :
    unitorHom N n ≫ unitorInv N n = 𝟙 (gradedTensor (GradedModule.regularModule A) N n) := by
  refine gradedTensor_hom_ext (GradedModule.regularModule A) N fun p X a y ↦ ?_
  have h₀ : 0 + p.1.1 + p.1.2 = n := by rw [zero_add]; exact p.2
  have e₁ : PresheafOfModules.Hom.app (unitorHom N n ≫ unitorInv N n).val X
        (tmul (GradedModule.regularModule A) N n p X a y) =
      tmul (GradedModule.regularModule A) N n (⟨(0, n), zero_add n⟩ : TensorIndex n) X
        (A.one.eval X)
        (gradedCast (fun k ↦ (N.piece k).val.obj X) p.2 (N.smul p.1.1 p.1.2 X a y)) :=
    (congrArg (fun z ↦ PresheafOfModules.Hom.app (unitorInv N n).val X z)
      (unitorHom_tmul N n p X a y)).trans (unitorInv_apply N n X _)
  have e₂ := tmul_cast_right (GradedModule.regularModule A) N p.2 ((zero_add _).trans p.2) X
    (A.one.eval X) (N.smul p.1.1 p.1.2 X a y)
  have e₃ := (tmulBalanced (GradedModule.regularModule A) N n).balanced
    (⟨(0, p.1.1, p.1.2), h₀⟩ : RelationIndex n) X (A.one.eval X) a y
  have e₄ : tmul (GradedModule.regularModule A) N n
        (leftIndex (⟨(0, p.1.1, p.1.2), h₀⟩ : RelationIndex n)) X
        ((A.mul 0 p.1.1).app X (A.one.eval X) a) y =
      tmul (GradedModule.regularModule A) N n p X a y :=
    (congrArg (fun z ↦ tmul (GradedModule.regularModule A) N n
        (leftIndex (⟨(0, p.1.1, p.1.2), h₀⟩ : RelationIndex n)) X z y)
      (eq_gradedCast_of_heq (Y := fun k ↦ ((GradedModule.regularModule A).piece k).val.obj X)
      (zero_add p.1.1).symm (A.one_mul p.1.1 X a))).trans
      (tmul_cast_left (GradedModule.regularModule A) N (zero_add p.1.1).symm p.2 X a y)
  exact e₁.trans ((e₂.trans e₃.symm).trans e₄)

/-- **The unit isomorphism of the relative tensor product**: `A ⊗_A N ≅ N` in degree `n`, for `A`
a sheaf of graded algebras acting on itself on the right and `N` a left graded `A`-module. -/
@[stacks 0FR2 "the unit isomorphism A ⊗_A N ≅ N of the relative tensor product, in degree n"]
noncomputable def unitorIso (n : ℤ) :
    gradedTensor (GradedModule.regularModule A) N n ≅ N.piece n where
  hom := unitorHom N n
  inv := unitorInv N n
  hom_inv_id := unitorHom_comp_unitorInv N n
  inv_hom_id := unitorInv_comp_unitorHom N n

/-- The unitor `A ⊗_A N → N` is an isomorphism in each degree. -/
instance isIso_unitorHom (n : ℤ) : IsIso (unitorHom N n) :=
  ⟨unitorInv N n, unitorHom_comp_unitorInv N n, unitorInv_comp_unitorHom N n⟩

end Sheafify

/-! ### Naturality and flatness -/

section Flat

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- **The unitor is natural in the left graded module.** -/
theorem unitorHom_naturality {N N' : LeftGradedModule.{t, m, m} A} (f : N ⟶ N') (n : ℤ) :
    gradedTensorMap (GradedModule.regularModule A) f n ≫ unitorHom N' n =
      unitorHom N n ≫ f.app n := by
  refine gradedTensor_hom_ext (GradedModule.regularModule A) N fun p X a y ↦ ?_
  refine Eq.trans ((congrArg (fun z ↦ PresheafOfModules.Hom.app (unitorHom N' n).val X z)
    (gradedTensorMap_tmul (GradedModule.regularModule A) f n p X a y)).trans
      (unitorHom_tmul N' n p X a _)) ?_
  refine Eq.trans ?_ (congrArg (fun z ↦ PresheafOfModules.Hom.app (f.app n).val X z)
    (unitorHom_tmul N n p X a y)).symm
  refine Eq.trans ?_ (gradedCast_dependent
    (fun k (z : (N.piece k).val.obj X) ↦ PresheafOfModules.Hom.app (f.app k).val X z) p.2
      (N.smul p.1.1 p.1.2 X a y)).symm
  exact congrArg (gradedCast (fun k ↦ (N'.piece k).val.obj X) p.2)
    (f.map_smul p.1.1 p.1.2 X a y).symm

/-- **A sheaf of graded algebras is flat as a right graded module over itself.** The functor
`N ↦ A ⊗_A N` is isomorphic to the identity by `SheafOfModules.RelativeTensor.unitorIso`, so it
carries a degreewise short exact sequence to a degreewise short exact sequence. -/
@[stacks 0FR2 "the regular right graded module is flat, by the unit isomorphism"]
theorem isGradedFlat_regularModule (A : GradedAlgebra.{t, m} (toRingCat J Osharp)) :
    IsGradedFlat (GradedModule.regularModule A) := by
  intro N₁ N₂ N₃ f g hfg hSE n
  have nat₁ := unitorHom_naturality f n
  have nat₂ := unitorHom_naturality g n
  have hz : gradedTensorMap (GradedModule.regularModule A) f n ≫
      gradedTensorMap (GradedModule.regularModule A) g n = 0 := by
    refine (cancel_mono (unitorHom N₃ n)).mp ?_
    rw [Category.assoc, nat₂, ← Category.assoc, nat₁, Category.assoc, hfg n, comp_zero,
      zero_comp]
  refine ⟨hz, ?_⟩
  exact (ShortComplex.shortExact_iff_of_iso (ShortComplex.isoMk (unitorIso N₁ n)
    (unitorIso N₂ n) (unitorIso N₃ n) nat₁.symm nat₂.symm)).mpr (hSE n)

end Flat

end RelativeTensor

end SheafOfModules
