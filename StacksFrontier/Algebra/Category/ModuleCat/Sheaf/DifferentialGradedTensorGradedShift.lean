module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackGradedShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensor

/-!
# The tensor product of a homogeneous family of right graded modules

Let `𝒜` and `ℬ` be sheaves of differential graded algebras on a site, let `𝒩` be a differential
graded `(𝒜, ℬ)`-bimodule and let `- ⊗_𝒜 𝒩` be a tensor product functor for `𝒩`, given by the
universal property of `SheafOfModules.TensorFunctorData`. A tensor product is characterised by
its degree-`n` local homomorphisms for *every* `n`, so a right-linear family of *any* degree `k`,

`𝒳^p ⟶ 𝒴^{p + k}`,

has a transport `(𝒳 ⊗_𝒜 𝒩)^p ⟶ (𝒴 ⊗_𝒜 𝒩)^{p + k}` through the functor, determined on local
sections by `x ⊗ y ↦ (g x) ⊗ y`, and the transport preserves identities, composites, sums and
zero.

## Main definitions

* `SheafOfModules.LocalHom.ofGradedShift` reads a degree-`k` right-linear family between the
  underlying graded modules of two right differential graded modules as a degree-`k` local
  homomorphism over an object of the site. A degree-`k` family out of `M` into `N` is a
  homomorphism of graded modules `M ⟶ N.shift k`, which is how every statement below spells it.
* `SheafOfModules.TensorFunctorData.shiftBilinear`,
  `SheafOfModules.TensorFunctorData.shiftLocalHom` and
  `SheafOfModules.TensorFunctorData.shiftHom` are the balanced bilinear family
  `(x, y) ↦ (g x) ⊗ y` of degree `k`, the degree-`k` local homomorphism it descends to, and the
  resulting degreewise map of sheaves of modules.
* `SheafOfModules.TensorFunctorData.gradedShiftMap` is **the transport of a degree-`k`
  right-linear family through the tensor product functor `- ⊗_𝒜 𝒩`.**

## Main results

* `SheafOfModules.TensorFunctorData.gradedShiftMap_tmul`: the transport sends `x ⊗ y` to
  `(g x) ⊗ y`, and `SheafOfModules.TensorFunctorData.gradedShiftMap_ext`: a degree-`k` family
  out of a tensor product is determined by its values on the image of the multiplication map.
  Together these determine the transport.
* `SheafOfModules.TensorFunctorData.gradedShiftMap_shiftComp`,
  `gradedShiftMap_shiftOfHom`, `gradedShiftMap_zero` and `gradedShiftMap_add`: the transport
  preserves composites, carries the degree-zero family of a morphism of right differential
  graded modules to the degree-zero family of its tensor product, and is additive.

## Implementation notes

The construction is the one of `SheafOfModules.IsTensorProduct.descend`, run in degree `k`
instead of degree zero: the balanced bilinear family `(x, y) ↦ (g x) ⊗ y` of degree `k` is
written down by hand, the universal property of the tensor product in degree `k` turns it into a
local homomorphism over each object of the site, and those are glued into a degreewise morphism
of sheaves of modules by evaluating at the identity of the object, compatibility with
restriction coming from `TensorFunctorData.restrict_shiftLocalHom`. That the glued family is
right-linear is the `isLinear` clause of the local homomorphisms, read in the second spelling
`(p + k) + i` of the degree `(p + i) + k`.

Uniqueness is `TensorFunctorData.gradedShiftMap_ext`, whose target graded module is arbitrary;
the four compatibility results below are all proved by it together with
`TensorFunctorData.gradedShiftMap_tmul` and the description `TensorFunctorData.map_spec` of the
functor on morphisms, so none of them needs the construction again.

The degrees `p + k + l` and `p + (k + l)` are propositionally but not definitionally equal, so
`SheafOfModules.GradedModule.shiftComp` takes the total degree as a parameter together with an
equation, and the degree transports `SheafOfModules.castHom` and `SheafOfModules.degCastHom`
move between the two spellings. For the same reason the characterising formula
`gradedShiftMap_tmul` carries the transport from `i + k + j`, the degree in which `(g x) ⊗ y`
is born, to `i + j + k`, the degree the transport lands in.

## References

* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
-/

@[expose] public section

open CategoryTheory

universe t a m w z s v u

namespace SheafOfModules

section Degrees

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- A degree-`n` map of the underlying graded modules absorbs a transport of the source degree
along an equality of degrees. -/
theorem LocalGradedHom.app_castHom_source {K : DifferentialGradedModule.{t, a, m} A}
    {L : DifferentialGradedModule.{t, a, s} A} {n : ℤ} {U : C} (f : LocalGradedHom K L n U)
    {i i' j : ℤ} (hi : i = i') (hij : i + n = j) (hij' : i' + n = j) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    f.app i' j hij' V (castHom K.complex.X hi (Opposite.op V.left) x) =
      f.app i j hij V x := by
  subst hi; rfl

/-- The value of a degree-`n` map of the underlying graded modules in two spellings of its
target degree differ by the transport along the equality of the two spellings. -/
theorem LocalGradedHom.app_castHom_target {K : DifferentialGradedModule.{t, a, m} A}
    {L : DifferentialGradedModule.{t, a, s} A} {n : ℤ} {U : C} (f : LocalGradedHom K L n U)
    {i j j' : ℤ} (hjj' : j = j') (hij : i + n = j) (hij' : i + n = j') (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    f.app i j' hij' V x =
      castHom L.complex.X hjj' (Opposite.op V.left) (f.app i j hij V x) := by
  subst hjj'; rfl

/-- The degree-`i` component of a degree-`k` right-linear family between the underlying graded
modules of two right differential graded modules, with the degree `i + k` it lands in written
out. The two spellings of that degree are definitionally equal, and this is the one the
multiplication map of a tensor product is stated in. -/
def DifferentialGradedModule.shiftApp {K L : DifferentialGradedModule.{t, a, w} A} (k : ℤ)
    (α : (forgetToGradedModule A).obj K ⟶ ((forgetToGradedModule A).obj L).shift k) (i : ℤ) :
    K.complex.X i ⟶ L.complex.X (i + k) :=
  α.app i

/-- The degree-`i` component of a degree-`k` right-linear family, with its target degree
written out, acts on local sections as the family does. -/
theorem DifferentialGradedModule.homSections_shiftApp
    {K L : DifferentialGradedModule.{t, a, w} A} (k : ℤ)
    (α : (forgetToGradedModule A).obj K ⟶ ((forgetToGradedModule A).obj L).shift k) (i : ℤ)
    (U : Cᵒᵖ) (x : (K.complex.X i).val.obj U) :
    homSections (DifferentialGradedModule.shiftApp k α i) U x = homSections (α.app i) U x :=
  rfl

variable {K L : DifferentialGradedModule.{t, a, s} A}

/-- **A degree-`k` right-linear family between the underlying graded modules of two right
differential graded modules, read as a degree-`k` local homomorphism** over an object of the
site: the value in degree `i` is the degree-`i` component of the family, transported from the
degree `i + k` in which it lands to the requested target degree. -/
def LocalHom.ofGradedShift (k : ℤ)
    (α : (forgetToGradedModule A).obj K ⟶
      ((forgetToGradedModule A).obj L).shift k) (U : C) :
    LocalHom K L k U where
  app i j hij V := (castHom L.complex.X hij (Opposite.op V.left)).comp
    (homSections (α.app i) (Opposite.op V.left))
  map_smul i j hij V r x := by
    refine Eq.trans (congrArg (castHom L.complex.X hij (Opposite.op V.left))
      (homSections_smul (α.app i) (Opposite.op V.left) r x)) ?_
    exact castHom_smul L.complex.X hij (Opposite.op V.left) r _
  naturality i j hij {V W} q x := by
    refine Eq.trans (castHom_naturality L.complex.X hij q.left.op _) ?_
    exact congrArg (castHom L.complex.X hij (Opposite.op W.left))
      (homSections_naturality (α.app i) q.left.op x)
  isLinear i j hij p V x b := by
    have e : homSections (α.app (i + p)) (Opposite.op V.left)
          ((K.mul i p).app (Opposite.op V.left) x b) =
        castHom L.complex.X (show i + k + p = i + p + k by omega) (Opposite.op V.left)
          ((L.mul (i + k) p).app (Opposite.op V.left)
            (homSections (α.app i) (Opposite.op V.left) x) b) :=
      (α.map_smul i p (Opposite.op V.left) x b).trans
        (GradedModule.shift_smul
          ((forgetToGradedModule A).obj L) k i p
          (Opposite.op V.left) _ b)
    refine Eq.trans (congrArg (castHom L.complex.X (show i + p + k = j + p by omega)
      (Opposite.op V.left)) e) ?_
    refine Eq.trans (castHom_castHom L.complex.X _ _ (Opposite.op V.left) _) ?_
    exact (mul_app_castHom L hij p (Opposite.op V.left) _ b).symm

/-- The local homomorphism attached to a degree-`k` right-linear family acts on a local section
through the degree-`i` component of the family. -/
@[simp]
theorem LocalHom.ofGradedShift_app (k : ℤ)
    (α : (forgetToGradedModule A).obj K ⟶
      ((forgetToGradedModule A).obj L).shift k) (U : C) (i j : ℤ)
    (hij : i + k = j) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    (LocalHom.ofGradedShift k α U).app i j hij V x =
      castHom L.complex.X hij (Opposite.op V.left)
        (homSections (α.app i) (Opposite.op V.left) x) :=
  rfl

end Degrees

section GradedShift

variable {C : Type u} [Category.{v} C] [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{t}}

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R} {M N Q : GradedModule.{t, a, m} A}

/-- The degree-`i` component of a degree-`k` right-linear family carries the action of a
homogeneous section of the algebra to the action of that same section, up to the equality of the
two spellings `(n + k) + i` and `(n + i) + k` of the degree it lands in. -/
theorem shiftHom_smul_heq (k : ℤ) (g : M ⟶ N.shift k) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.piece n).val.obj U) (y : (A.piece i).val.obj U) :
    HEq (homSections (g.app (n + i)) U (M.smul n i U x y))
      (N.smul (n + k) i U (homSections (g.app n) U x) y) :=
  (heq_of_eq ((g.map_smul n i U x y).trans (shift_smul N k n i U _ y))).trans
    (heq_castHom N.piece _ U _)

/-- The degree-`i` component of a composite of two right-linear families is the composite of
their components, transported from `i + k + l` to the total degree. -/
theorem homSections_shiftComp {k l j : ℤ} (hj : k + l = j) (g : M ⟶ N.shift k)
    (g' : N ⟶ Q.shift l) (i : ℤ) (U : Cᵒᵖ) (x : (M.piece i).val.obj U) :
    homSections ((shiftComp hj g g').app i) U x =
      castHom Q.piece (show i + k + l = i + j by omega) U
        (homSections (g'.app (i + k)) U (homSections (g.app i) U x)) :=
  homSections_degCastHom Q.piece _ U _

/-- The degree-`i` component of the degree-zero family of a homomorphism of graded modules is
that homomorphism, transported from `i` to `i + 0`. -/
theorem homSections_shiftOfHom (f : M ⟶ N) (i : ℤ) (U : Cᵒᵖ)
    (x : (M.piece i).val.obj U) :
    homSections ((shiftOfHom f).app i) U x =
      castHom N.piece (show i = i + 0 by omega) U (homSections (f.app i) U x) :=
  homSections_degCastHom N.piece _ U _

end GradedModule

end GradedShift

section Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A B}

namespace IsTensorProduct

variable {M : DifferentialGradedModule.{t, a, m} A} {T : DifferentialGradedModule.{t, a, s} B}

/-- The multiplication map of a tensor product respects a heterogeneous equality between two
homogeneous sections in propositionally equal degrees in its first variable. -/
theorem tmul_heq_left (hT : IsTensorProduct M N T) {i i' : ℤ} (hi : i = i') (j : ℤ) (U : Cᵒᵖ)
    {x : (M.complex.X i).val.obj U} {x' : (M.complex.X i').val.obj U} (hx : HEq x x')
    (y : (N.complex.X j).val.obj U) :
    HEq (hT.tmul i j U x y) (hT.tmul i' j U x' y) := by
  subst hi
  rw [eq_of_heq hx]

/-- The multiplication map of a tensor product absorbs a transport of the degree of its first
variable. -/
theorem tmul_castHom_left (hT : IsTensorProduct M N T) {i i' : ℤ} (hi : i = i') (j : ℤ)
    (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    hT.tmul i' j U (castHom M.complex.X hi U x) y =
      castHom T.complex.X (by omega : i + j = i' + j) U (hT.tmul i j U x y) := by
  subst hi; rfl

end IsTensorProduct

namespace TensorFunctorData

open DifferentialGradedModule

variable (D : TensorFunctorData.{t, a, m, z, s} A B N)
  {X Y Z : DifferentialGradedModule.{t, a, m} A}

/-- The balanced bilinear family `(x, y) ↦ (g x) ⊗ y` of degree `k` attached to a degree-`k`
right-linear family `g` between the underlying graded modules of two right differential graded
`𝒜`-modules. -/
def shiftBilinear (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C) :
    LocalBalancedBilinear X N (D.functor.obj Y) k U where
  app i j kk hijk V :=
    castHom₂ (X.complex.X i) (N.complex.X j) (D.functor.obj Y).complex.X
      (show i + k + j = kk by omega) (Opposite.op V.left)
      (((D.isTensorProduct Y).tmul (i + k) j (Opposite.op V.left)).comp
        (homSections (shiftApp k g i) (Opposite.op V.left)))
  map_smul_left i j kk hijk V r x y := by
    simp only [castHom₂_apply, AddMonoidHom.coe_comp, Function.comp_apply, homSections_smul]
    rw [(D.isTensorProduct Y).tmul_smul_left, castHom_smul]
  map_smul_right i j kk hijk V r x y := by
    simp only [castHom₂_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [(D.isTensorProduct Y).tmul_smul_right, castHom_smul]
  naturality i j kk hijk {V W} q x y := by
    have e1 := castHom₂_apply (X.complex.X i) (N.complex.X j) (D.functor.obj Y).complex.X
      (show i + k + j = kk by omega) (Opposite.op V.left)
      (((D.isTensorProduct Y).tmul (i + k) j (Opposite.op V.left)).comp
        (homSections (shiftApp k g i) (Opposite.op V.left))) x y
    have e2 := castHom₂_apply (X.complex.X i) (N.complex.X j) (D.functor.obj Y).complex.X
      (show i + k + j = kk by omega) (Opposite.op W.left)
      (((D.isTensorProduct Y).tmul (i + k) j (Opposite.op W.left)).comp
        (homSections (shiftApp k g i) (Opposite.op W.left)))
      ((X.complex.X i).val.map q.left.op x) ((N.complex.X j).val.map q.left.op y)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at e1 e2
    rw [e1, castHom_naturality, (D.isTensorProduct Y).tmul_naturality, homSections_naturality]
    exact e2.symm
  balanced i p j kk hijk V x a y := by
    simp only [castHom₂_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    refine castHom_heq (D.functor.obj Y).complex.X _ _ _ (HEq.trans ?_
      ((D.isTensorProduct Y).tmul_balanced (i + k) p j (Opposite.op V.left)
        (homSections (shiftApp k g i) (Opposite.op V.left) x) a y))
    exact (D.isTensorProduct Y).tmul_heq_left (show i + p + k = i + k + p by omega) j
      (Opposite.op V.left)
      (GradedModule.shiftHom_smul_heq k g i p (Opposite.op V.left) x a) y
  map_rightMul i j p kk hijk V x y b := by
    simp only [castHom₂_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [mul_app_castHom]
    exact castHom_heq (D.functor.obj Y).complex.X _ _ _
      ((D.isTensorProduct Y).tmul_rightMul (i + k) j p (Opposite.op V.left) _ y b).symm

/-- The balanced bilinear family attached to a degree-`k` right-linear family sends `(x, y)` to
`(g x) ⊗ y`. -/
@[simp]
theorem shiftBilinear_app (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C)
    (i j kk : ℤ) (hijk : i + j + k = kk) (V : Over U)
    (x : (X.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (D.shiftBilinear k g U).app i j kk hijk V x y =
      castHom (D.functor.obj Y).complex.X (show i + k + j = kk by omega) (Opposite.op V.left)
        ((D.isTensorProduct Y).tmul (i + k) j (Opposite.op V.left)
          (homSections (g.app i) (Opposite.op V.left) x) y) :=
  castHom₂_apply (X.complex.X i) (N.complex.X j) (D.functor.obj Y).complex.X _
    (Opposite.op V.left) _ x y

/-- The degree-`k` local homomorphism `𝒳 ⊗_𝒜 𝒩 → 𝒴 ⊗_𝒜 𝒩` determined by
`x ⊗ y ↦ (g x) ⊗ y` for a degree-`k` right-linear family `g`. -/
noncomputable def shiftLocalHom (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C) :
    LocalHom (D.functor.obj X) (D.functor.obj Y) k U :=
  ((D.isTensorProduct X).universal (D.functor.obj Y) k U).symm (D.shiftBilinear k g U)

/-- Composing the tensor product of a degree-`k` right-linear family with the multiplication map
returns the balanced bilinear family it was built from. -/
theorem universal_shiftLocalHom (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C) :
    (D.isTensorProduct X).universal (D.functor.obj Y) k U (D.shiftLocalHom k g U) =
      D.shiftBilinear k g U :=
  ((D.isTensorProduct X).universal (D.functor.obj Y) k U).apply_symm_apply _

/-- The tensor product of a degree-`k` right-linear family sends `x ⊗ y` to `(g x) ⊗ y`. -/
theorem shiftLocalHom_tmul (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (U : C)
    (i j kk : ℤ) (hijk : i + j + k = kk) (V : Over U)
    (x : (X.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (D.shiftLocalHom k g U).app (i + j) kk hijk V
        ((D.isTensorProduct X).tmul i j (Opposite.op V.left) x y) =
      castHom (D.functor.obj Y).complex.X (show i + k + j = kk by omega) (Opposite.op V.left)
        ((D.isTensorProduct Y).tmul (i + k) j (Opposite.op V.left)
          (homSections (g.app i) (Opposite.op V.left) x) y) := by
  have h2 : ((D.isTensorProduct X).universal (D.functor.obj Y) k U
      (D.shiftLocalHom k g U)).app i j kk hijk V x y =
      (D.shiftBilinear k g U).app i j kk hijk V x y := by
    rw [D.universal_shiftLocalHom k g U]
  rw [(D.isTensorProduct X).universal_app, D.shiftBilinear_app] at h2
  exact h2

/-- The tensor product of a degree-`k` right-linear family is compatible with restriction along
a morphism of the site. -/
theorem restrict_shiftLocalHom (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k)
    {U U' : C} (q : U' ⟶ U) :
    (D.shiftLocalHom k g U).restrict q = D.shiftLocalHom k g U' := by
  refine ((D.isTensorProduct X).universal (D.functor.obj Y) k U').injective
    (LocalBalancedBilinear.ext fun i j kk hijk V x y => ?_)
  rw [(D.isTensorProduct X).universal_restrict (D.functor.obj Y) k q
      (D.shiftLocalHom k g U) i j kk hijk V x y,
    D.universal_shiftLocalHom k g U, D.universal_shiftLocalHom k g U',
    D.shiftBilinear_app, D.shiftBilinear_app]
  rfl

/-- The map on sections over an object of the site given by the tensor product of a degree-`k`
right-linear family. -/
noncomputable def shiftSections (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (n : ℤ)
    (U : Cᵒᵖ) :
    ((D.functor.obj X).complex.X n).val.obj U →+
      ((D.functor.obj Y).complex.X (n + k)).val.obj U :=
  (D.shiftLocalHom k g U.unop).app n (n + k) rfl (Over.mk (𝟙 U.unop))

/-- The tensor product of a degree-`k` right-linear family commutes with restriction. -/
theorem shiftSections_naturality (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (n : ℤ)
    {U V : Cᵒᵖ} (γ : U ⟶ V) (x : ((D.functor.obj X).complex.X n).val.obj U) :
    ((D.functor.obj Y).complex.X (n + k)).val.map γ (D.shiftSections k g n U x) =
      D.shiftSections k g n V (((D.functor.obj X).complex.X n).val.map γ x) := by
  have hA := (D.shiftLocalHom k g U.unop).naturality n (n + k) rfl
    (Over.homMk γ.unop (Category.comp_id γ.unop) :
      Over.mk γ.unop ⟶ Over.mk (𝟙 U.unop)) x
  refine hA.trans ?_
  refine (LocalGradedHom.app_mk_congr (D.shiftLocalHom k g U.unop).toLocalGradedHom n (n + k)
    rfl (Category.id_comp γ.unop).symm
    (((D.functor.obj X).complex.X n).val.map γ x)).trans ?_
  exact LocalHom.app_congr (D.restrict_shiftLocalHom k g γ.unop) n (n + k) rfl
    (Over.mk (𝟙 V.unop)) (((D.functor.obj X).complex.X n).val.map γ x)

/-- The degreewise map of sheaves of modules given by the tensor product of a degree-`k`
right-linear family. -/
noncomputable def shiftHom (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (n : ℤ) :
    (D.functor.obj X).complex.X n ⟶ (D.functor.obj Y).complex.X (n + k) where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => D.shiftSections k g n U x
          map_add' := fun x y => map_add _ x y
          map_smul' := fun r x => (D.shiftLocalHom k g U.unop).map_smul n (n + k) rfl
            (Over.mk (𝟙 U.unop)) r x }
      naturality := fun {U V} γ => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        exact (D.shiftSections_naturality k g n γ x).symm }

/-- The degreewise map given by the tensor product of a degree-`k` right-linear family acts on
local sections through the degree-`k` local homomorphism it descends from. -/
theorem shiftHom_apply (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (n : ℤ)
    (U : Cᵒᵖ) (x : ((D.functor.obj X).complex.X n).val.obj U) :
    (D.shiftHom k g n).val.app U x = D.shiftSections k g n U x := rfl

/-- **The transport of a degree-`k` right-linear family through the tensor product functor
`- ⊗_𝒜 𝒩`**: the degree-`k` right-linear family of the two tensor products determined by
`x ⊗ y ↦ (g x) ⊗ y`. -/
noncomputable def gradedShiftMap (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) :
    (forgetToGradedModule B).obj (D.functor.obj X) ⟶
      ((forgetToGradedModule B).obj (D.functor.obj Y)).shift k where
  app n := D.shiftHom k g n
  map_smul n i U x y := by
    refine Eq.trans (LocalGradedHom.app_castHom_target
      (D.shiftLocalHom k g U.unop).toLocalGradedHom
      (show n + k + i = n + i + k by omega) (by omega) (by omega) (Over.mk (𝟙 U.unop))
      (((D.functor.obj X).mul n i).app U x y)) ?_
    refine Eq.trans ?_ (GradedModule.shift_smul
      ((forgetToGradedModule B).obj (D.functor.obj Y)) k n i U _ y).symm
    refine congrArg (castHom (D.functor.obj Y).complex.X
      (show n + k + i = n + i + k by omega) U) ?_
    exact (D.shiftLocalHom k g U.unop).isLinear n (n + k) rfl i (Over.mk (𝟙 U.unop)) x y

/-- **The transport of a degree-`k` right-linear family sends `x ⊗ y` to `(g x) ⊗ y`**, the
value being born in degree `i + k + j` and transported to the degree `i + j + k` of the
transport. This determines the transport, by `gradedShiftMap_ext`. -/
theorem gradedShiftMap_tmul (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (i j : ℤ)
    (U : Cᵒᵖ) (x : (X.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    homSections ((D.gradedShiftMap k g).app (i + j)) U
        ((D.isTensorProduct X).tmul i j U x y) =
      castHom (D.functor.obj Y).complex.X (show i + k + j = i + j + k by omega) U
        ((D.isTensorProduct Y).tmul (i + k) j U (homSections (g.app i) U x) y) :=
  D.shiftLocalHom_tmul k g U.unop i j (i + j + k) rfl (Over.mk (𝟙 U.unop)) x y

/-- **A degree-`k` right-linear family out of a tensor product is determined by its values on
the image of the multiplication map.** -/
theorem gradedShiftMap_ext (k : ℤ)
    {α β : (forgetToGradedModule B).obj (D.functor.obj X) ⟶
      ((forgetToGradedModule B).obj (D.functor.obj Y)).shift k}
    (h : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (X.complex.X i).val.obj U)
        (y : (N.complex.X j).val.obj U),
      homSections (α.app (i + j)) U ((D.isTensorProduct X).tmul i j U x y) =
        homSections (β.app (i + j)) U ((D.isTensorProduct X).tmul i j U x y)) :
    α = β := by
  have key : ∀ U : C, LocalHom.ofGradedShift k α U = LocalHom.ofGradedShift k β U := fun U =>
    (D.isTensorProduct X).localHom_ext fun i j kk hijk V x y => by
      refine Eq.trans (LocalHom.ofGradedShift_app k α U (i + j) kk hijk V _) ?_
      refine Eq.trans ?_ (LocalHom.ofGradedShift_app k β U (i + j) kk hijk V _).symm
      exact congrArg (castHom (D.functor.obj Y).complex.X hijk (Opposite.op V.left))
        (h i j (Opposite.op V.left) x y)
  refine GradedModule.Hom.ext fun p => ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact LocalHom.app_congr (key U.unop) p (p + k) rfl (Over.mk (𝟙 U.unop)) x

/-- The transport of a degree-`k` right-linear family sends `x ⊗ y` to `w ⊗ y`, where `w` is any
rewriting of the value of the family at `x`. -/
private theorem gradedShiftMap_tmul_of_eq (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (i j : ℤ)
    (U : Cᵒᵖ) (x : (X.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U)
    {w : (Y.complex.X (i + k)).val.obj U} (hw : homSections (g.app i) U x = w) :
    homSections ((D.gradedShiftMap k g).app (i + j)) U ((D.isTensorProduct X).tmul i j U x y) =
      castHom (D.functor.obj Y).complex.X (show i + k + j = i + j + k by omega) U
        ((D.isTensorProduct Y).tmul (i + k) j U w y) := by
  subst hw
  exact D.gradedShiftMap_tmul k g i j U x y

/-- Variant of `gradedShiftMap_tmul_of_eq` where the value of the family at `x` is a transport of
a section `v` along an equality of degrees. -/
private theorem gradedShiftMap_tmul_of_eq_castHom (k : ℤ)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) (i j m : ℤ)
    (U : Cᵒᵖ) (x : (X.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) (hm : m = i + k)
    (v : (Y.complex.X m).val.obj U) (hv : homSections (g.app i) U x = castHom Y.complex.X hm U v) :
    homSections ((D.gradedShiftMap k g).app (i + j)) U ((D.isTensorProduct X).tmul i j U x y) =
      castHom (D.functor.obj Y).complex.X (show m + j = i + j + k by omega) U
        ((D.isTensorProduct Y).tmul m j U v y) := by
  refine (D.gradedShiftMap_tmul_of_eq k g i j U x y hv).trans ?_
  rw [(D.isTensorProduct Y).tmul_castHom_left hm j U v y, castHom_castHom]

/-- **The transport of a composite of two right-linear families is the composite of the
transports.** -/
theorem gradedShiftMap_shiftComp {k l j : ℤ} (hj : k + l = j)
    (g : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k)
    (g' : (forgetToGradedModule A).obj Y ⟶ ((forgetToGradedModule A).obj Z).shift l) :
    D.gradedShiftMap j (GradedModule.shiftComp hj g g') =
      GradedModule.shiftComp hj (D.gradedShiftMap k g) (D.gradedShiftMap l g') := by
  refine D.gradedShiftMap_ext j fun i p U x y => ?_
  refine Eq.trans (D.gradedShiftMap_tmul_of_eq_castHom j (GradedModule.shiftComp hj g g') i p
    (i + k + l) U x y (by omega) _ (GradedModule.homSections_shiftComp hj g g' i U x)) ?_
  refine Eq.trans ?_ (GradedModule.homSections_shiftComp hj (D.gradedShiftMap k g)
    (D.gradedShiftMap l g') (i + p) U ((D.isTensorProduct X).tmul i p U x y)).symm
  refine Eq.trans ?_ (congrArg (castHom (D.functor.obj Z).complex.X
    (show i + p + k + l = i + p + j by omega) U) (congrArg
      (homSections ((D.gradedShiftMap l g').app (i + p + k)) U)
      (D.gradedShiftMap_tmul k g i p U x y)).symm)
  refine Eq.trans ?_ (congrArg (castHom (D.functor.obj Z).complex.X
    (show i + p + k + l = i + p + j by omega) U)
    (GradedModule.app_castHom (D.gradedShiftMap l g')
      (show i + k + p = i + p + k by omega) U _).symm)
  refine Eq.trans ?_ (congrArg (castHom (D.functor.obj Z).complex.X
      (show i + p + k + l = i + p + j by omega) U)
    (GradedModule.castHom_shift_piece ((forgetToGradedModule B).obj (D.functor.obj Z)) l
      (show i + k + p = i + p + k by omega) U _).symm)
  refine Eq.trans ?_ (congrArg (castHom (D.functor.obj Z).complex.X
      (show i + p + k + l = i + p + j by omega) U)
    (congrArg (castHom (D.functor.obj Z).complex.X
      (show i + k + p + l = i + p + k + l by omega) U)
      (D.gradedShiftMap_tmul l g' (i + k) p U (homSections (g.app i) U x) y))).symm
  refine Eq.trans ?_ (congrArg (castHom (D.functor.obj Z).complex.X
      (show i + p + k + l = i + p + j by omega) U)
    (castHom_castHom (D.functor.obj Z).complex.X _ _ U _)).symm
  exact (castHom_castHom (D.functor.obj Z).complex.X _ _ U _).symm

/-- **The transport of the degree-zero family of a morphism of right differential graded modules
is the degree-zero family of its tensor product.** -/
theorem gradedShiftMap_shiftOfHom (h : X ⟶ Y) :
    D.gradedShiftMap 0 (GradedModule.shiftOfHom ((forgetToGradedModule A).map h)) =
      GradedModule.shiftOfHom ((forgetToGradedModule B).map (D.functor.map h)) := by
  refine D.gradedShiftMap_ext 0 fun i p U x y => ?_
  refine Eq.trans (D.gradedShiftMap_tmul_of_eq_castHom 0
    (GradedModule.shiftOfHom ((forgetToGradedModule A).map h)) i p i U x y (by omega) _
    (GradedModule.homSections_shiftOfHom ((forgetToGradedModule A).map h) i U x)) ?_
  refine Eq.trans ?_ (GradedModule.homSections_shiftOfHom
    ((forgetToGradedModule B).map (D.functor.map h)) (i + p) U
    ((D.isTensorProduct X).tmul i p U x y)).symm
  exact congrArg (castHom (D.functor.obj Y).complex.X (show i + p = i + p + 0 by omega) U)
    (D.map_spec h i p U x y).symm

/-- **The transport of the zero family is zero.** -/
theorem gradedShiftMap_zero (k : ℤ) :
    D.gradedShiftMap k (0 : (forgetToGradedModule A).obj X ⟶
      ((forgetToGradedModule A).obj Y).shift k) = 0 := by
  refine D.gradedShiftMap_ext k fun i p U x y => ?_
  refine Eq.trans (D.gradedShiftMap_tmul_of_eq k 0 i p U x y (homSections_zero U x)) ?_
  refine Eq.trans (congrArg (castHom (D.functor.obj Y).complex.X
    (show i + k + p = i + p + k by omega) U)
    ((D.isTensorProduct Y).tmul_zero_left (i + k) p U y)) ?_
  exact (map_zero _).trans (homSections_zero U ((D.isTensorProduct X).tmul i p U x y)).symm

/-- **The transport of a sum of two right-linear families is the sum of the transports.** -/
theorem gradedShiftMap_add (k : ℤ)
    (g g' : (forgetToGradedModule A).obj X ⟶ ((forgetToGradedModule A).obj Y).shift k) :
    D.gradedShiftMap k (g + g') = D.gradedShiftMap k g + D.gradedShiftMap k g' := by
  refine D.gradedShiftMap_ext k fun i p U x y => ?_
  refine Eq.trans (D.gradedShiftMap_tmul_of_eq k (g + g') i p U x y
    (homSections_add (g.app i) (g'.app i) U x)) ?_
  refine Eq.trans (congrArg (castHom (D.functor.obj Y).complex.X
    (show i + k + p = i + p + k by omega) U)
    ((D.isTensorProduct Y).tmul_add_left (i + k) p U _ _ y)) ?_
  refine Eq.trans (castHom_add (D.functor.obj Y).complex.X _ U _ _) ?_
  refine Eq.trans (congrArg₂ (· + ·) (D.gradedShiftMap_tmul k g i p U x y).symm
    (D.gradedShiftMap_tmul k g' i p U x y).symm) ?_
  exact (homSections_add ((D.gradedShiftMap k g).app (i + p))
    ((D.gradedShiftMap k g').app (i + p)) U ((D.isTensorProduct X).tmul i p U x y)).symm

end TensorFunctorData

end Tensor

end SheafOfModules

end
