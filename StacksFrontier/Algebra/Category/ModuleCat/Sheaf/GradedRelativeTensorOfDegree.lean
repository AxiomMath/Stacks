module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHomSheaf

/-!
# The functor `- ⊗_A N` on homomorphisms of degree `d`

Let `O` be a sheaf of commutative rings on a site, let `A` be a sheaf of graded `O`-algebras and
let `N` be a left graded `A`-module. The functor `- ⊗_A N` from right graded `A`-modules to
graded `O`-modules (`SheafOfModules.RelativeTensor.gradedTensorFunctor`) upgrades to a functor of
graded categories `Mod^gr(A) → Gr^gr(Mod(O))`: a homomorphism `f : P → P'` homogeneous of degree
`d` induces the map of degree `d` from `P ⊗_A N` to `P' ⊗_A N` sending `x ⊗ y` to `f(x) ⊗ y`.

## Main definitions

* `SheafOfModules.RelativeTensor.Balanced.ofHomOfDegree` is the balanced bilinear family
  `(x, y) ↦ f(x) ⊗ y`.
* `SheafOfModules.RelativeTensor.gradedTensorMapRightOfDegree f N hk` is the component
  `(P ⊗_A N)^n → (P' ⊗_A N)^k`, where `n + d = k`, of the map of degree `d` induced by `f`.

## Main results

* `SheafOfModules.RelativeTensor.gradedTensorMapRightOfDegree_tmul` computes it on `x ⊗ y`.
* `SheafOfModules.RelativeTensor.gradedTensorMapRightOfDegree_comp` is compatibility with the
  composition `Hom^e(P', P'') × Hom^d(P, P') → Hom^{d + e}(P, P'')` of Tag 0FR1.
* `SheafOfModules.RelativeTensor.gradedTensorMapRightOfDegree_eq_gradedTensorMapRight` identifies
  the map induced by a homomorphism of degree `0` with the functoriality of
  `SheafOfModules.RelativeTensor.gradedTensorFunctor`, and
  `SheafOfModules.RelativeTensor.gradedTensorMapRightOfDegree_id` is compatibility with
  identities.

## Implementation notes

The degree `d` map is given componentwise, `(P ⊗_A N)^n → (P' ⊗_A N)^k` for every `n + d = k`,
the same convention as `SheafOfModules.GradedHomOfDegree`; this avoids transport along
`n + d + e = n + (d + e)` in the composition law.

## References

* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe v u t m

namespace SheafOfModules

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

section OfDegree

variable {P P' : GradedModule.{t, m, m} A} {d : ℤ} (f : GradedHomOfDegree P P' d)
  (N : LeftGradedModule.{t, m, m} A)

/-- The local section `f(x) ⊗ y` does not depend on how the degree of `f(x)` is written. -/
theorem tmul_app_congr {i j j' q k : ℤ} (hj : i + d = j) (hj' : i + d = j') (hq : j + q = k)
    (hq' : j' + q = k) (X : Cᵒᵖ) (x : (P.piece i).val.obj X) (y : (N.piece q).val.obj X) :
    tmul P' N k ⟨(j, q), hq⟩ X ((f.app i j hj).val.app X x) y =
      tmul P' N k ⟨(j', q), hq'⟩ X ((f.app i j' hj').val.app X x) y := by
  obtain rfl : j = j' := by omega
  rfl

/-- The bilinear map `(x, y) ↦ f(x) ⊗ y` from `P^p × N^q` into degree `k` of `P' ⊗_A N`, for
a homomorphism `f : P → P'` homogeneous of degree `d`, `p + q = n` and `n + d = k`. -/
noncomputable def ofHomOfDegreeApp {n k : ℤ} (hk : n + d = k) (p : TensorIndex n) :
    Stacks.BilinearMap (P.piece p.1.1).val (N.piece p.1.2).val (gradedTensor P' N k).val :=
  PresheafOfModules.toBilinear
    (PresheafOfModules.tensorHom (f.app p.1.1 (p.1.1 + d) rfl).val (𝟙 (N.piece p.1.2).val) ≫
      tensorSumι P' N (⟨(p.1.1 + d, p.1.2), by have := p.2; omega⟩ : TensorIndex k) ≫
        gradedTensorπ P' N k ≫ gradedTensorUnit P' N k)

/-- `SheafOfModules.RelativeTensor.ofHomOfDegreeApp` sends `(x, y)` to the local section
`f(x) ⊗ y`. -/
theorem ofHomOfDegreeApp_app {n k : ℤ} (hk : n + d = k) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    (ofHomOfDegreeApp f N hk p).app X x y =
      tmul P' N k ⟨(p.1.1 + d, p.1.2), by have := p.2; omega⟩ X
        ((f.app p.1.1 (p.1.1 + d) rfl).val.app X x) y :=
  congrArg (fun z ↦ PresheafOfModules.Hom.app (tensorSumι P' N
      (⟨(p.1.1 + d, p.1.2), by have := p.2; omega⟩ : TensorIndex k) ≫
        gradedTensorπ P' N k ≫ gradedTensorUnit P' N k) X z)
    (PresheafOfModules.tensorHom_tmul _ _ X x y)

/-- The balanced bilinear family `(x, y) ↦ f(x) ⊗ y` of total degree `n`, into degree `k` of
`P' ⊗_A N`, for a homomorphism `f : P → P'` homogeneous of degree `d` and `n + d = k`. -/
noncomputable def Balanced.ofHomOfDegree {n k : ℤ} (hk : n + d = k) :
    Balanced P N (gradedTensor P' N k).val n where
  app p := ofHomOfDegreeApp f N hk p
  balanced i X x a y := by
    rw [ofHomOfDegreeApp_app, ofHomOfDegreeApp_app]
    have hi := i.2
    have e₁ := tmul_app_congr f N (i := i.1.1 + i.1.2.1) (j := i.1.1 + i.1.2.1 + d)
      (j' := i.1.1 + d + i.1.2.1) (q := i.1.2.2) (k := k) rfl (by omega) (by omega) (by omega)
      X (P.smul i.1.1 i.1.2.1 X x a) y
    have e₂ := f.map_mul i.1.1 (i.1.1 + d) rfl i.1.2.1 X x a
    have e₃ : tmul P' N k ⟨(i.1.1 + d + i.1.2.1, i.1.2.2), by omega⟩ X
        (P'.smul (i.1.1 + d) i.1.2.1 X ((f.app i.1.1 (i.1.1 + d) rfl).val.app X x) a) y =
      tmul P' N k ⟨(i.1.1 + d, i.1.2.1 + i.1.2.2), by omega⟩ X
        ((f.app i.1.1 (i.1.1 + d) rfl).val.app X x) (N.smul i.1.2.1 i.1.2.2 X a y) :=
      (tmulBalanced P' N k).balanced (⟨(i.1.1 + d, i.1.2.1, i.1.2.2), by
        change i.1.1 + d + i.1.2.1 + i.1.2.2 = k; omega⟩ : RelationIndex k) X
        ((f.app i.1.1 (i.1.1 + d) rfl).val.app X x) a y
    refine e₁.trans (Eq.trans ?_ e₃)
    rw [e₂]

/-- The bilinear maps of `SheafOfModules.RelativeTensor.Balanced.ofHomOfDegree` send `(x, y)` to
the local section `f(x) ⊗ y`. -/
theorem Balanced.ofHomOfDegree_app {n k : ℤ} (hk : n + d = k) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    ((Balanced.ofHomOfDegree f N hk).app p).app X x y =
      tmul P' N k ⟨(p.1.1 + d, p.1.2), by have := p.2; omega⟩ X
        ((f.app p.1.1 (p.1.1 + d) rfl).val.app X x) y :=
  ofHomOfDegreeApp_app f N hk p X x y

/-- **`- ⊗_A N` on homomorphisms of degree `d`.** The component `(P ⊗_A N)^n → (P' ⊗_A N)^k`,
for `n + d = k`, of the map of degree `d` induced by a homomorphism `f : P → P'` of right graded
`A`-modules homogeneous of degree `d`; it sends `x ⊗ y` to `f(x) ⊗ y`. -/
@[stacks 0FR2 "`- ⊗_A N` as a functor of graded categories: the map of degree `d` induced by a \
homomorphism of degree `d`"]
noncomputable def gradedTensorMapRightOfDegree {n k : ℤ} (hk : n + d = k) :
    gradedTensor P N n ⟶ gradedTensor P' N k :=
  (Balanced.ofHomOfDegree f N hk).desc P N

/-- The map of degree `d` induced by `f` sends the local section `x ⊗ y` to `f(x) ⊗ y`. -/
theorem gradedTensorMapRightOfDegree_tmul {n k : ℤ} (hk : n + d = k) (p : TensorIndex n)
    (X : Cᵒᵖ) (x : (P.piece p.1.1).val.obj X) (y : (N.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (gradedTensorMapRightOfDegree f N hk).val X (tmul P N n p X x y) =
      tmul P' N k ⟨(p.1.1 + d, p.1.2), by have := p.2; omega⟩ X
        ((f.app p.1.1 (p.1.1 + d) rfl).val.app X x) y :=
  (Balanced.desc_tmul P N _ p X x y).trans (Balanced.ofHomOfDegree_app f N hk p X x y)

/-- **A homomorphism of degree `0` induces the map of `- ⊗_A N`.** If `f` is homogeneous of
degree `0` with components those of a homomorphism `h` of right graded modules, the map of
degree `0` it induces is `SheafOfModules.RelativeTensor.gradedTensorMapRight h N`. -/
theorem gradedTensorMapRightOfDegree_eq_gradedTensorMapRight (f : GradedHomOfDegree P P' 0)
    (h : P ⟶ P') (hf : ∀ i, f.app i i (add_zero i) = h.app i) (n : ℤ) :
    gradedTensorMapRightOfDegree f N (add_zero n) = gradedTensorMapRight h N n := by
  refine gradedTensor_hom_ext P N fun p X x y ↦ ?_
  refine (gradedTensorMapRightOfDegree_tmul f N (add_zero n) p X x y).trans ?_
  refine (tmul_app_congr f N rfl (add_zero p.1.1) _ p.2 X x y).trans ?_
  rw [hf]
  exact (gradedTensorMapRight_tmul h N n p X x y).symm

end OfDegree

/-- **`- ⊗_A N` preserves identities of the graded category.** A homomorphism of degree `0`
from `P` to itself whose components are identities induces the identity of `P ⊗_A N`. -/
theorem gradedTensorMapRightOfDegree_id {P : GradedModule.{t, m, m} A}
    (N : LeftGradedModule.{t, m, m} A) (f : GradedHomOfDegree P P 0)
    (hf : ∀ i, f.app i i (add_zero i) = 𝟙 _) (n : ℤ) :
    gradedTensorMapRightOfDegree f N (add_zero n) = 𝟙 (gradedTensor P N n) :=
  (gradedTensorMapRightOfDegree_eq_gradedTensorMapRight N f (𝟙 P) hf n).trans
    (gradedTensorMapRight_id N n)

/-- **`- ⊗_A N` preserves composition of the graded category.** For `f : P → P'` homogeneous of
degree `d` and `g : P' → P''` homogeneous of degree `e`, the map of degree `d + e` induced by the
composite `g ∘ f` is the composite of the maps induced by `f` and by `g`. -/
@[stacks 0FR2 "`- ⊗_A N` as a functor of graded categories: compatibility with composition"]
theorem gradedTensorMapRightOfDegree_comp {P P' P'' : GradedModule.{t, m, m} A} {d e : ℤ}
    (f : GradedHomOfDegree P P' d) (g : GradedHomOfDegree P' P'' e)
    (N : LeftGradedModule.{t, m, m} A) {n j k : ℤ} (hj : n + d = j) (hk : j + e = k) :
    gradedTensorMapRightOfDegree (g.comp f) N (show n + (d + e) = k by omega) =
      gradedTensorMapRightOfDegree f N hj ≫ gradedTensorMapRightOfDegree g N hk := by
  refine gradedTensor_hom_ext P N fun p X x y ↦ ?_
  refine (gradedTensorMapRightOfDegree_tmul (g.comp f) N _ p X x y).trans ?_
  rw [GradedHomOfDegree.comp_app]
  refine (tmul_app_congr g N (i := p.1.1 + d) (j := p.1.1 + (d + e)) (j' := p.1.1 + d + e)
    (by omega) rfl _ (by have := p.2; omega) X ((f.app p.1.1 (p.1.1 + d) rfl).val.app X x)
      y).trans ?_
  exact ((congrArg (PresheafOfModules.Hom.app (gradedTensorMapRightOfDegree g N hk).val X)
    (gradedTensorMapRightOfDegree_tmul f N hj p X x y)).trans
      (gradedTensorMapRightOfDegree_tmul g N hk
        ⟨(p.1.1 + d, p.1.2), by have := p.2; omega⟩ X _ y)).symm

end RelativeTensor

end SheafOfModules
