module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHomModule
public import StacksCore.Tactic.StacksAttribute

/-!
# The functor `- ⊗_A N` into right graded `B`-modules

Let `(C, O)` be a ringed site, let `A` and `B` be sheaves of graded `O`-algebras and let `N` be a
graded `(A, B)`-bimodule. For a right graded `A`-module `M` the graded tensor product `M ⊗_A N`
of [Stacks, Tag 0FR2] is a right graded `B`-module,
`SheafOfModules.RelativeTensor.gradedTensorRight`, with `(x ⊗ y) b = x ⊗ (y b)`. Following
[Stacks, Tag 0FR4], `- ⊗_A N` is a functor `Mod(A) ⥤ Mod(B)` and a functor of graded
categories `Mod^gr(A) → Mod^gr(B)`, sending a homomorphism `f : M → M'` homogeneous of degree `n`
to the induced homomorphism `M ⊗_A N → M' ⊗_A N` of degree `n`, `x ⊗ y ↦ f(x) ⊗ y`. The
functor and its action on homogeneous homomorphisms are defined in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleToposPullback.lean`; both carry the
Stacks 0FR4 tag there. This file proves the laws of a functor of graded categories.

## Main definitions

* `SheafOfModules.RelativeTensor.gradedTensorRightFunctor N` (defined and tagged 0FR4 in
  `GradedModuleToposPullback`): **the functor `- ⊗_A N : Mod(A) ⥤ Mod(B)`**, acting on
  morphisms by `SheafOfModules.RelativeTensor.gradedTensorRightHom N h`.
* `SheafOfModules.RelativeTensor.gradedTensorRightHomOfDegree N f` (defined and tagged 0FR4 in
  `GradedModuleToposPullback`): the homomorphism `M ⊗_A N → M' ⊗_A N` homogeneous of degree `n`
  induced by a homomorphism `f` of degree `n`.
* `SheafOfModules.RelativeTensor.gradedTensorRightHomOfDegreeLinear N`: the same map as a
  homomorphism of `Γ(C, O)`-modules `Hom^n(M, M') → Hom^n(M ⊗_A N, M' ⊗_A N)`.

## Main results

* `SheafOfModules.RelativeTensor.gradedTensorRightHom_tmul` (in `GradedModuleToposPullback`) and
  `gradedTensorRightHomOfDegree_tmul`: on a local section, `x ⊗ y ↦ f(x) ⊗ y`.
* `SheafOfModules.RelativeTensor.gradedTensorRightHom_app`: the underlying morphisms of graded
  `O`-modules are those of the functor `- ⊗_A N` of [Stacks, Tag 0FR2].
* `SheafOfModules.RelativeTensor.gradedTensorRightHomOfDegree_comp` and
  `gradedTensorRightHomOfDegree_ofHom`: `- ⊗_A N` preserves the composition of the graded
  categories, and in degree `0` it is `gradedTensorRightFunctor`, so it preserves identities.
  With `gradedTensorRightHomOfDegreeLinear` this makes `- ⊗_A N` a functor of graded categories
  `Mod^gr(A) → Mod^gr(B)` over `Γ(C, O)`.

## Implementation notes

The setting is that of `SheafOfModules.RelativeTensor.gradedTensorRight`: the base is a sheaf of
commutative rings, the homogeneous pieces of the algebras and the sections of the modules are in
the universe `max u v z`, and the site carries sheafification of abelian presheaves in that
universe. The induced homomorphisms are the descents
`SheafOfModules.RelativeTensor.BalancedRight.descRight` of the balanced families
`(x, y) ↦ f(x) ⊗ y`; a homomorphism of degree `n` is first read as a degree-zero homomorphism into
the shift `(M' ⊗_A N)⟨n⟩` (`SheafOfModules.GradedHomOfDegree.shiftHomEquiv`).

## References

* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe t z v u

namespace SheafOfModules

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A B : GradedAlgebra.{t, max u v z} (toRingCat J Osharp)}
  (N : GradedBimodule.{t, max u v z, max u v z} A B)
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]
  [HasWeakSheafify J AddCommGrpCat.{max u v z}]
  {M M' M'' : GradedModule.{t, max u v z, max u v z} A}

/-- The rings of sections of the sheaf of rings underlying a sheaf of commutative rings are
commutative. -/
local instance isMulCommutative_toRingCat_obj (U : Cᵒᵖ) :
    IsMulCommutative ((toRingCat J Osharp).obj.obj U) :=
  inferInstanceAs (IsMulCommutative (Osharp.obj.obj U))

open GradedHomOfDegree in
/-- The homogeneous homomorphisms of degree `n` between right graded `A`-modules, with their
action of `Γ(C, O)`, at the sheaf of rings `toRingCat J Osharp`. -/
noncomputable local instance smulGlobalSectionRing
    (P Q : GradedModule.{t, max u v z, max u v z} A) (n : ℤ) :
    SMul (Stacks.Cohomology.SiteModules.GlobalSectionRing (toRingCat J Osharp))
      (GradedHomOfDegree P Q n) :=
  instSMulSubtypeForallCarrierObjOppositeRingCatObjFunctorIsSheafMemSubringGlobalSectionRing
    (R := toRingCat J Osharp)

open GradedHomOfDegree in
/-- The homogeneous homomorphisms of degree `n` between right graded `A`-modules form a
`Γ(C, O)`-module, at the sheaf of rings `toRingCat J Osharp`. -/
noncomputable local instance moduleGlobalSectionRing
    (P Q : GradedModule.{t, max u v z, max u v z} A) (n : ℤ) :
    Module (Stacks.Cohomology.SiteModules.GlobalSectionRing (toRingCat J Osharp))
      (GradedHomOfDegree P Q n) :=
  instModuleSubtypeForallCarrierObjOppositeRingCatObjFunctorIsSheafMemSubringGlobalSectionRing
    (R := toRingCat J Osharp)

/-! ### Index bookkeeping for local sections `x ⊗ y` -/

/-- Two local sections `x ⊗ y` whose left factors are heterogeneously equal agree. -/
theorem tmul_congr_left {P : GradedModule.{t, max u v z, max u v z} A}
    {L : LeftGradedModule.{t, max u v z, max u v z} A} {n a a' b : ℤ} (h : a + b = n)
    (h' : a' + b = n) (X : Cᵒᵖ) {x : (P.piece a).val.obj X} {x' : (P.piece a').val.obj X}
    (hx : HEq x x') (y : (L.piece b).val.obj X) :
    tmul P L n ⟨(a, b), h⟩ X x y = tmul P L n ⟨(a', b), h'⟩ X x' y := by
  obtain rfl : a = a' := by omega
  obtain rfl := eq_of_heq hx
  rfl

/-- Two morphisms out of degree `n` of `M ⊗_A N` which agree on all local sections `x ⊗ y` are
equal. -/
theorem gradedTensorRight_piece_hom_ext {K : SheafOfModules.{max u v z} (toRingCat J Osharp)}
    {n : ℤ} {φ ψ : (gradedTensorRight M N).piece n ⟶ K}
    (h : ∀ (p : TensorIndex n) (X : Cᵒᵖ) (x : (M.piece p.1.1).val.obj X)
        (y : (N.toLeftGradedModule.piece p.1.2).val.obj X),
      φ.val.app X (tmul M N.toLeftGradedModule n p X x y) =
        ψ.val.app X (tmul M N.toLeftGradedModule n p X x y)) :
    φ = ψ :=
  gradedTensor_hom_ext M N.toLeftGradedModule h

/-- Two homomorphisms out of `M ⊗_A N` which agree on all local sections `x ⊗ y` are equal. -/
theorem gradedTensorRight_hom_ext {K : GradedModule.{t, max u v z, max u v z} B}
    {φ ψ : gradedTensorRight M N ⟶ K}
    (h : ∀ (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ) (x : (M.piece p.1.1).val.obj X)
        (y : (N.toLeftGradedModule.piece p.1.2).val.obj X),
      (φ.app n).val.app X (tmul M N.toLeftGradedModule n p X x y) =
        (ψ.app n).val.app X (tmul M N.toLeftGradedModule n p X x y)) :
    φ = ψ :=
  GradedModule.Hom.ext fun n => gradedTensorRight_piece_hom_ext N (h n)

/-! ### The functor `- ⊗_A N : Mod(A) ⥤ Mod(B)` -/

/-- The morphisms of graded `O`-modules underlying `gradedTensorRightHom N h` are those of the
functor `- ⊗_A N` of Stacks 0FR2. -/
theorem gradedTensorRightHom_app (h : M ⟶ M') (n : ℤ) :
    (gradedTensorRightHom N h).app n = gradedTensorMapRight h N.toLeftGradedModule n :=
  gradedTensorRight_piece_hom_ext N fun p X x y =>
    (gradedTensorRightHom_tmul N h n p X x y).trans
      (gradedTensorMapRight_tmul h N.toLeftGradedModule n p X x y).symm

/-- The functor `- ⊗_A N` sends `h` to `gradedTensorRightHom N h`. -/
@[simp]
theorem gradedTensorRightFunctor_map (h : M ⟶ M') :
    (gradedTensorRightFunctor N).map h = gradedTensorRightHom N h := rfl

/-! ### The functor of graded categories `- ⊗_A N : Mod^gr(A) → Mod^gr(B)` -/

variable {n m : ℤ}

/-- `gradedTensorRightHomOfDegree N f` sends `x ⊗ y` to `f(x) ⊗ y`. -/
theorem gradedTensorRightHomOfDegree_tmul (f : GradedHomOfDegree M M' n) (k j : ℤ)
    (hkj : k + n = j) (p : TensorIndex k) (X : Cᵒᵖ) (x : (M.piece p.1.1).val.obj X)
    (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    ((gradedTensorRightHomOfDegree N f).app k j hkj).val.app X
        (tmul M N.toLeftGradedModule k p X x y) =
      tmul M' N.toLeftGradedModule j ⟨(p.1.1 + n, p.1.2), by have := p.2; omega⟩ X
        ((f.app p.1.1 (p.1.1 + n) rfl).val.app X x) y := by
  change homSections (degCastHom (gradedTensorRight M' N).piece hkj) X
      (((homOfDegreeBalancedRight N f).descRight.app k).val.app X
        (tmul M N.toLeftGradedModule k p X x y)) = _
  rw [homSections_degCastHom, BalancedRight.descRight_tmul]
  exact castHom_tmul M' N.toLeftGradedModule hkj ⟨(p.1.1 + n, p.1.2), by have := p.2; omega⟩ X _ y

/-- **`- ⊗_A N` preserves composition in the graded categories**:
`(g ∘ f) ⊗ N = (g ⊗ N) ∘ (f ⊗ N)`. -/
theorem gradedTensorRightHomOfDegree_comp (f : GradedHomOfDegree M M' n)
    (g : GradedHomOfDegree M' M'' m) :
    gradedTensorRightHomOfDegree N (g.comp f) =
      (gradedTensorRightHomOfDegree N g).comp (gradedTensorRightHomOfDegree N f) := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  refine gradedTensorRight_piece_hom_ext N fun p X x y => ?_
  have key : ((gradedTensorRightHomOfDegree N g).app (i + n) j (by omega)).val.app X
      (((gradedTensorRightHomOfDegree N f).app i (i + n) rfl).val.app X
        (tmul M N.toLeftGradedModule i p X x y)) =
      tmul M'' N.toLeftGradedModule j ⟨(p.1.1 + n + m, p.1.2), by have := p.2; omega⟩ X
        ((g.app (p.1.1 + n) (p.1.1 + n + m) rfl).val.app X
          ((f.app p.1.1 (p.1.1 + n) rfl).val.app X x)) y := by
    rw [gradedTensorRightHomOfDegree_tmul N f, gradedTensorRightHomOfDegree_tmul N g]
  rw [gradedTensorRightHomOfDegree_tmul, GradedHomOfDegree.comp_app]
  exact (tmul_congr_left _ _ X (g.app_heq _ _ rfl X HEq.rfl) y).trans key.symm

/-- `- ⊗_A N` is additive on homogeneous homomorphisms of degree `n`. -/
theorem gradedTensorRightHomOfDegree_add (f f' : GradedHomOfDegree M M' n) :
    gradedTensorRightHomOfDegree N (f + f') =
      gradedTensorRightHomOfDegree N f + gradedTensorRightHomOfDegree N f' := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  refine gradedTensorRight_piece_hom_ext N fun p X x y => ?_
  have key : ((gradedTensorRightHomOfDegree N f).app i j hij +
        (gradedTensorRightHomOfDegree N f').app i j hij).val.app X
        (tmul M N.toLeftGradedModule i p X x y) =
      tmul M' N.toLeftGradedModule j ⟨(p.1.1 + n, p.1.2), by have := p.2; omega⟩ X
          ((f.app p.1.1 (p.1.1 + n) rfl).val.app X x) y +
        tmul M' N.toLeftGradedModule j ⟨(p.1.1 + n, p.1.2), by have := p.2; omega⟩ X
          ((f'.app p.1.1 (p.1.1 + n) rfl).val.app X x) y := by
    change ((gradedTensorRightHomOfDegree N f).app i j hij).val.app X
        (tmul M N.toLeftGradedModule i p X x y) +
      ((gradedTensorRightHomOfDegree N f').app i j hij).val.app X
        (tmul M N.toLeftGradedModule i p X x y) = _
    rw [gradedTensorRightHomOfDegree_tmul, gradedTensorRightHomOfDegree_tmul]
    rfl
  rw [gradedTensorRightHomOfDegree_tmul, GradedHomOfDegree.add_app, GradedHomOfDegree.add_app,
    key]
  exact ((tmulBalanced M' N.toLeftGradedModule j).app
    ⟨(p.1.1 + n, p.1.2), by have := p.2; omega⟩).map_add_left X _ _ y

/-- `- ⊗_A N` is linear over the global sections `Γ(C, O)` on homogeneous homomorphisms of
degree `n`. -/
theorem gradedTensorRightHomOfDegree_smul
    (c : Stacks.Cohomology.SiteModules.GlobalSectionRing (toRingCat J Osharp))
    (f : GradedHomOfDegree M M' n) :
    gradedTensorRightHomOfDegree N (c • f) = c • gradedTensorRightHomOfDegree N f := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  refine gradedTensorRight_piece_hom_ext N fun p X x y => ?_
  have key : ((c • gradedTensorRightHomOfDegree N f).app i j hij).val.app X
        (tmul M N.toLeftGradedModule i p X x y) =
      c.1 X • tmul M' N.toLeftGradedModule j ⟨(p.1.1 + n, p.1.2), by have := p.2; omega⟩ X
        ((f.app p.1.1 (p.1.1 + n) rfl).val.app X x) y :=
    (GradedHomOfDegree.smul_app_apply c _ i j hij X _).trans
      (congrArg (c.1 X • ·) (gradedTensorRightHomOfDegree_tmul N f i j hij p X x y))
  rw [gradedTensorRightHomOfDegree_tmul, GradedHomOfDegree.smul_app_apply, key]
  exact ((tmulBalanced M' N.toLeftGradedModule j).app
    ⟨(p.1.1 + n, p.1.2), by have := p.2; omega⟩).map_smul_left X _ _ y

/-- **Stacks 0FR4: `- ⊗_A N` is a functor of graded categories over `Γ(C, O)`, on the morphisms
of degree `n`**: the map `Hom^n(M, M') → Hom^n(M ⊗_A N, M' ⊗_A N)` is `Γ(C, O)`-linear. Its
compatibility with composition is
`SheafOfModules.RelativeTensor.gradedTensorRightHomOfDegree_comp`, and with identities
`SheafOfModules.RelativeTensor.gradedTensorRightHomOfDegree_ofHom`. -/
@[stacks 0FR4 "- ⊗_A N is Γ(C, O)-linear on Hom^n, as a functor of graded categories"]
noncomputable def gradedTensorRightHomOfDegreeLinear
    (M M' : GradedModule.{t, max u v z, max u v z} A) (n : ℤ) :
    GradedHomOfDegree M M' n →ₗ[Stacks.Cohomology.SiteModules.GlobalSectionRing
        (toRingCat J Osharp)]
      GradedHomOfDegree (gradedTensorRight M N) (gradedTensorRight M' N) n where
  toFun := gradedTensorRightHomOfDegree N
  map_add' := gradedTensorRightHomOfDegree_add N
  map_smul' := gradedTensorRightHomOfDegree_smul N

/-- **In degree `0`, `- ⊗_A N` on the graded categories is the functor
`- ⊗_A N : Mod(A) ⥤ Mod(B)`.** In particular it sends identities to identities. -/
theorem gradedTensorRightHomOfDegree_ofHom (h : M ⟶ M') :
    gradedTensorRightHomOfDegree N (GradedHomOfDegree.ofHom h) =
      GradedHomOfDegree.ofHom (gradedTensorRightHom N h) := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  refine gradedTensorRight_piece_hom_ext N fun p X x y => ?_
  exact (gradedTensorRightHomOfDegree_tmul N (GradedHomOfDegree.ofHom h) i j hij p X x y).trans
    ((tmul_congr_left _ _ X ((heq_of_eq (GradedHomOfDegree.ofHom_app_apply h _ _ rfl X x)).trans
        (heq_castHom _ _ _ _)) y).trans
      ((GradedHomOfDegree.ofHom_app_apply (gradedTensorRightHom N h) i j hij X _).trans
        ((congrArg (castHom (gradedTensorRight M' N).piece (by omega : i = j) X)
            (gradedTensorRightHom_tmul N h i p X x y)).trans
          (castHom_tmul M' N.toLeftGradedModule (by omega : i = j) p X _ y))).symm)

end RelativeTensor

end SheafOfModules
