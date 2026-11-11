module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestriction

/-!
# Extension of scalars is left adjoint to restriction of scalars

Let `R` be a sheaf of rings on a site and let `φ : A ⟶ B` be a unit-preserving homomorphism of
sheaves of differential graded `R`-algebras. Restriction of scalars

`res_φ : Mod(B, d) ⥤ Mod(A, d)`

is `SheafOfModules.DifferentialGradedModule.restriction`, and the same `φ` makes `B` into a
differential graded `(A, B)`-bimodule `{}_A B_B`, which is
`SheafOfModules.DifferentialGradedAlgebra.Hom.toBimodule`. Extension of scalars is the tensor
product with that bimodule,

`- ⊗_{A, φ} B : Mod(A, d) ⥤ Mod(B, d)`,

and this file proves that it is left adjoint to `res_φ`, which is the second assertion of
[Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP).

## Main results

* `SheafOfModules.DifferentialGradedModule.extensionRestrictionAdjunction`: the adjunction
  `- ⊗_{A, φ} B ⊣ res_φ`.
* `SheafOfModules.DifferentialGradedModule.extensionRestrictionHomEquiv`: the hom-set bijection
  it is built from, `Hom_{Mod(B, d)}(M ⊗_{A, φ} B, L) ≃ Hom_{Mod(A, d)}(M, res_φ L)`, given by
  `g ↦ (x ↦ g (x ⊗ 1))`.
* `SheafOfModules.DifferentialGradedModule.extensionUnit`: its unit `x ↦ x ⊗ 1`, and
  `SheafOfModules.DifferentialGradedModule.extensionUnit_naturality` its naturality.
* `SheafOfModules.DifferentialGradedModule.extensionDescendHom`: the inverse bijection, the
  homomorphism `M ⊗_{A, φ} B ⟶ L` determined by `x ⊗ b ↦ f (x) b`.

## Main definitions

* `SheafOfModules.LocalHom.ofDgHom` reads a homomorphism of right differential graded modules
  as a degree-zero local homomorphism over an object of the site.
* `SheafOfModules.LocalHom.diffDefect` is the degree-one local homomorphism `d ∘ h - h ∘ d`
  attached to a degree-zero local homomorphism `h`; it vanishes exactly when `h` commutes with
  the differentials.
* `SheafOfModules.DifferentialGradedModule.extensionDescendBalanced` reads a homomorphism
  `f : M ⟶ res_φ L` as the `A`-balanced bilinear family `(x, b) ↦ f (x) b` of degree zero,
  which is the half of the adjunction supplied by the universal property of the tensor
  product.

## Implementation notes

**The tensor product enters through its universal property.** Everything below is stated for
a `SheafOfModules.TensorFunctorData A B (φ.toBimodule hφ)`: a functor `Mod(A, d) ⥤ Mod(B, d)`
whose value at `M` *is* a tensor product `M ⊗_A {}_A B_B` in the sense of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensor.lean`, together with the
description `x ⊗ y ↦ f (x) ⊗ y` of its action on morphisms. The proof uses only that universal
property, so it applies to any such functor and works over an arbitrary sheaf of rings and in
arbitrary universes. The library constructs one,
`SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight`, and the adjunction for it,
with nothing carried, is
`SheafOfModules.DifferentialGradedModule.baseChangeRestrictionAdjunction` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedBaseChangeAdjunction.lean`.

**Unit preservation is a hypothesis.** As in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedRestriction.lean`, Definition
[Stacks, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF) does not require a homomorphism
of sheaves of differential graded algebras to preserve the unit, while `res_φ L` is not a right
differential graded `A`-module unless it does. So
`SheafOfModules.DifferentialGradedAlgebra.Hom.PreservesOne` is carried explicitly here too, and
it is also what makes the unit `x ↦ x ⊗ 1` of the adjunction `A`-linear.

**How the bijection is built.** The universal property of the tensor product is a bijection
between the degree-`n` *local* homomorphisms out of `M ⊗_A N` over an object `U` of the site
and the `A`-balanced bilinear families of degree `n` over `U`. The adjunction is a bijection of
*global* homomorphisms, so the argument has two halves. The local half is
`SheafOfModules.DifferentialGradedModule.extensionDescendBalanced`: a homomorphism
`f : M ⟶ res_φ L` yields the balanced family `(x, b) ↦ f (x) b`, which is balanced because
`f (x a) = f (x) φ(a)` and `B`-linear on the right because the action of `L` is associative.
The global half assembles the resulting local homomorphisms into a morphism of complexes,
exactly as the comparison of two tensor products is assembled in
`DifferentialGradedTensor.lean`: compatibility with restriction comes from
`SheafOfModules.IsTensorProduct.universal_restrict`, and commutation with the differentials
from the vanishing of `SheafOfModules.LocalHom.diffDefect`, which is checked on the sections
`x ⊗ y` by the universal property and reduces to the signed Leibniz rules for `M ⊗_A N` and for
`L`.

The other direction of the bijection needs none of that: it is composition with the unit
`x ↦ x ⊗ 1`, which makes naturality in both variables cheap. Naturality in the source is
deduced from the naturality of the unit by injectivity of the bijection, and naturality in the
target is associativity of composition.

**Two spellings of one sheaf.** The underlying complex of `res_φ L` *is* the complex of `L`,
and the underlying complex of `{}_A B_B` *is* the complex of `B`; but `restrictionObj` and
`toBimodule` are definitions, so the two spellings of each sheaf are interchangeable only after
unfolding them. A term mixing the two spellings is then rejected by the congruence machinery of
`simp`. The identifications are therefore named —
`SheafOfModules.DifferentialGradedModule.restrictionHomComponent`,
`SheafOfModules.toBimoduleSection`, `SheafOfModules.toBimoduleOne`,
`SheafOfModules.toBimoduleMap` — so that every statement below is written in one spelling and
the unfolding happens once, inside the body of each of those definitions.

**Degrees.** The two conventions of the input files are kept. The multiplication map of a
tensor product has target degree `i + j` on the nose, so computations with it move between
spellings of a degree by `SheafOfModules.castHom`; a local homomorphism takes its target degree
as an independent argument with a proof, so no transport is needed for it. The unit lands in
degree `i + 0`, and that single transport is what most of the casts below are about.

**Universes.** The two algebras share the universe `a` of their homogeneous pieces because a
homomorphism relates them, and the module universe `m` is shared by the source and the target
of the two functors because they are adjoint. The site, the sheaf of rings, the algebras and
the modules are otherwise independent. The base is an arbitrary sheaf of rings on an arbitrary
site rather than the structure sheaf of a ringed site; a ringed site `X` is the case
`R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP) — restriction of
  scalars, the bimodule `{}_A B_B` and the adjunction proved here.
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM) — balanced bilinear
  families, the universal property of the tensor product.
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ) — differential graded
  bimodules.
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI) — right differential
  graded modules.
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF) — sheaves of
  differential graded algebras and their homomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a m w z v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Local homomorphisms attached to a homomorphism of differential graded modules -/

section LocalHoms

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- A homomorphism of right differential graded modules commutes with the transport of local
sections along an equality of degrees. -/
theorem DifferentialGradedModule.f_app_castHom
    {K L : DifferentialGradedModule.{t, a, m} A} (g : K ⟶ L) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (K.complex.X i).val.obj U) :
    (g.toHomologicalComplex.f j).val.app U (castHom K.complex.X h U x) =
      castHom L.complex.X h U ((g.toHomologicalComplex.f i).val.app U x) := by
  subst h; rfl

/-- A homomorphism of right differential graded modules, read as a degree-zero local
homomorphism over an object of the site. -/
def LocalHom.ofDgHom {K L : DifferentialGradedModule.{t, a, m} A} (g : K ⟶ L) (U : C) :
    LocalHom K L 0 U where
  app i j hij V := (castHom L.complex.X ((add_zero i).symm.trans hij) (Opposite.op V.left)).comp
    (homSections (g.toHomologicalComplex.f i) (Opposite.op V.left))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, homSections_smul, castHom_smul]
  naturality i j hij {V W} q x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [castHom_naturality, homSections_naturality]
    rfl
  isLinear i j hij p V x b := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, homSections_apply]
    rw [g.map_mul i p (Opposite.op V.left) x b, mul_app_castHom]

/-- A homomorphism of right differential graded modules, read as a local homomorphism, acts on
a local section through its degreewise components. -/
theorem LocalHom.ofDgHom_app {K L : DifferentialGradedModule.{t, a, m} A} (g : K ⟶ L) (U : C)
    (i j : ℤ) (hij : i + 0 = j) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    (LocalHom.ofDgHom g U).app i j hij V x =
      castHom L.complex.X ((add_zero i).symm.trans hij) (Opposite.op V.left)
        ((g.toHomologicalComplex.f i).val.app (Opposite.op V.left) x) :=
  rfl

/-- A homomorphism of right differential graded modules is read as the same local homomorphism
over every object of the site. -/
theorem LocalHom.restrict_ofDgHom {K L : DifferentialGradedModule.{t, a, m} A} (g : K ⟶ L)
    {U U' : C} (q : U' ⟶ U) :
    (LocalHom.ofDgHom g U).restrict q = LocalHom.ofDgHom g U' :=
  LocalHom.ext fun _ _ _ _ _ => rfl

/-- The defect `d ∘ h - h ∘ d` of a degree-zero local homomorphism from commuting with the
differentials, as a degree-one local homomorphism: it is linear over the algebra because the
two signs produced by the Leibniz rules cancel. -/
def LocalHom.diffDefect {K : DifferentialGradedModule.{t, a, w} A}
    {L : DifferentialGradedModule.{t, a, z} A} {U : C} (h : LocalHom K L 0 U) :
    LocalHom K L 1 U where
  app i j hij V :=
    (homSections (L.complex.d i j) (Opposite.op V.left)).comp (h.app i i (add_zero i) V) -
      (h.app j j (add_zero j) V).comp (homSections (K.complex.d i j) (Opposite.op V.left))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      h.map_smul, homSections_smul, smul_sub]
  naturality i j hij {V W} q x := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [map_sub_sections]
    simp only [homSections_naturality, h.naturality]
    rfl
  isLinear i j hij p V x b := by
    subst hij
    have hd : i + p + 1 = i + 1 + p := by omega
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      homSections_apply, map_sub]
    rw [h.isLinear i i (add_zero i) p V x b,
      d_app_castHom L.complex hd (Opposite.op V.left),
      L.leibniz_castHom i p (Opposite.op V.left) (h.app i i (add_zero i) V x) b,
      d_app_castHom K.complex hd (Opposite.op V.left),
      K.leibniz_castHom i p (Opposite.op V.left) x b]
    simp only [map_add, map_zsmul, castHom_castHom, castHom_self]
    rw [LocalGradedHom.app_castHom h.toLocalGradedHom ((add_assoc i p 1).symm.trans hd) V _,
      h.isLinear (i + 1) (i + 1) (add_zero (i + 1)) p V
        ((K.complex.d i (i + 1)).val.app (Opposite.op V.left) x) b,
      h.isLinear i i (add_zero i) (p + 1) V x
        ((A.complex.d p (p + 1)).val.app (Opposite.op V.left) b)]
    abel

/-- The defect of a degree-zero local homomorphism from commuting with the differentials acts
on a local section `x` by `d (h x) - h (d x)`. -/
theorem LocalHom.diffDefect_app {K : DifferentialGradedModule.{t, a, w} A}
    {L : DifferentialGradedModule.{t, a, z} A} {U : C} (h : LocalHom K L 0 U) (i j : ℤ)
    (hij : i + 1 = j) (V : Over U) (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    h.diffDefect.app i j hij V x =
      (L.complex.d i j).val.app (Opposite.op V.left) (h.app i i (add_zero i) V x) -
        h.app j j (add_zero j) V ((K.complex.d i j).val.app (Opposite.op V.left) x) :=
  rfl

end LocalHoms

/-! ### The two spellings of the bimodule `{}_A B_B` and of a restriction of scalars -/

section Spellings

variable {A B : DifferentialGradedAlgebra.{t, a} R}

open DifferentialGradedAlgebra DifferentialGradedModule

/-- The multiplication map of a tensor product respects a heterogeneous equality between two
homogeneous sections in propositionally equal degrees in its second variable. -/
theorem IsTensorProduct.tmul_heq_right {M : DifferentialGradedModule.{t, a, w} A}
    {N : DifferentialGradedBimodule.{t, a, z} A B} {T : DifferentialGradedModule.{t, a, m} B}
    (hT : IsTensorProduct M N T) (i : ℤ) {j j' : ℤ} (hj : j = j') (U : Cᵒᵖ)
    (x : (M.complex.X i).val.obj U) {y : (N.complex.X j).val.obj U}
    {y' : (N.complex.X j').val.obj U} (hy : HEq y y') :
    HEq (hT.tmul i j U x y) (hT.tmul i j' U x y') := by
  subst hj
  rw [eq_of_heq hy]

/-- A homogeneous local section of the bimodule `{}_A B_B` attached to `φ`, read as a local
section of `B`: the underlying complex of the bimodule *is* the complex of `B`. -/
def toBimoduleSection (φ : A ⟶ B) (hφ : φ.PreservesOne) (j : ℤ) (U : Cᵒᵖ) :
    ((φ.toBimodule hφ).complex.X j).val.obj U →+ (B.complex.X j).val.obj U :=
  AddMonoidHom.id _

/-- The unit of `B`, read as a local section of the bimodule `{}_A B_B`. -/
def toBimoduleOne (φ : A ⟶ B) (hφ : φ.PreservesOne) (U : Cᵒᵖ) :
    ((φ.toBimodule hφ).complex.X 0).val.obj U :=
  B.one.eval U

/-- The image of a homogeneous local section of `A` under `φ`, read as a local section of the
bimodule `{}_A B_B`. -/
def toBimoduleMap (φ : A ⟶ B) (hφ : φ.PreservesOne) (i : ℤ) (U : Cᵒᵖ)
    (aa : (A.complex.X i).val.obj U) : ((φ.toBimodule hφ).complex.X i).val.obj U :=
  (φ.toHomologicalComplex.f i).val.app U aa

variable (φ : A ⟶ B) (hφ : φ.PreservesOne)

/-- Reading a section of `{}_A B_B` in `B` turns the left action of `a` into left multiplication
by `φ(a)`. -/
theorem toBimoduleSection_leftMul (p j : ℤ) (U : Cᵒᵖ) (aa : (A.complex.X p).val.obj U)
    (y : ((φ.toBimodule hφ).complex.X j).val.obj U) :
    toBimoduleSection φ hφ (p + j) U (((φ.toBimodule hφ).leftMul p j).app U aa y) =
      (B.mul p j).app U ((φ.toHomologicalComplex.f p).val.app U aa)
        (toBimoduleSection φ hφ j U y) :=
  rfl

/-- Reading a section of `{}_A B_B` in `B` turns the right action into multiplication in `B`. -/
theorem toBimoduleSection_rightMul (j p : ℤ) (U : Cᵒᵖ)
    (y : ((φ.toBimodule hφ).complex.X j).val.obj U) (b : (B.complex.X p).val.obj U) :
    toBimoduleSection φ hφ (j + p) U (((φ.toBimodule hφ).rightMul j p).app U y b) =
      (B.mul j p).app U (toBimoduleSection φ hφ j U y) b :=
  rfl

/-- Reading a section of `{}_A B_B` in `B` commutes with the differentials. -/
theorem toBimoduleSection_d (j j' : ℤ) (U : Cᵒᵖ)
    (y : ((φ.toBimodule hφ).complex.X j).val.obj U) :
    toBimoduleSection φ hφ j' U (((φ.toBimodule hφ).complex.d j j').val.app U y) =
      (B.complex.d j j').val.app U (toBimoduleSection φ hφ j U y) :=
  rfl

/-- Reading a section of `{}_A B_B` in `B` commutes with restriction along `g : U ⟶ V`. -/
theorem toBimoduleSection_naturality (j : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V)
    (y : ((φ.toBimodule hφ).complex.X j).val.obj U) :
    (B.complex.X j).val.map g (toBimoduleSection φ hφ j U y) =
      toBimoduleSection φ hφ j V (((φ.toBimodule hφ).complex.X j).val.map g y) :=
  rfl

/-- Reading a section of `{}_A B_B` in `B` is `R`-linear. -/
theorem toBimoduleSection_smul (j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (y : ((φ.toBimodule hφ).complex.X j).val.obj U) :
    toBimoduleSection φ hφ j U (r • y) = r • toBimoduleSection φ hφ j U y :=
  rfl

/-- The section `toBimoduleOne`, read in `B`, is the unit of `B`. -/
@[simp]
theorem toBimoduleSection_toBimoduleOne (U : Cᵒᵖ) :
    toBimoduleSection φ hφ 0 U (toBimoduleOne φ hφ U) = B.one.eval U :=
  rfl

/-- The section `toBimoduleMap φ hφ i U a`, read in `B`, is `φ(a)`. -/
@[simp]
theorem toBimoduleSection_toBimoduleMap (i : ℤ) (U : Cᵒᵖ)
    (aa : (A.complex.X i).val.obj U) :
    toBimoduleSection φ hφ i U (toBimoduleMap φ hφ i U aa) =
      (φ.toHomologicalComplex.f i).val.app U aa :=
  rfl

/-- The unit section of `{}_A B_B` is compatible with restriction along `g : U ⟶ V`. -/
theorem toBimoduleOne_naturality {U V : Cᵒᵖ} (g : U ⟶ V) :
    ((φ.toBimodule hφ).complex.X 0).val.map g (toBimoduleOne φ hφ U) = toBimoduleOne φ hφ V :=
  PresheafOfModules.sections_property B.one g

/-- The unit section of `{}_A B_B` is closed: `d 1 = 0`. -/
theorem toBimoduleOne_d (U : Cᵒᵖ) :
    ((φ.toBimodule hφ).complex.d 0 (0 + 1)).val.app U (toBimoduleOne φ hφ U) = 0 := by
  have h : (B.complex.d 0 (0 + 1)).val.app U (B.one.eval U) = 0 := by
    rw [d_app_castHom B.complex (show (1 : ℤ) = 0 + 1 from by omega) U, B.one_closed U]
    exact map_zero _
  exact h

/-- The unit of `B` acts as the identity on the left of the bimodule `{}_A B_B`. -/
theorem heq_leftMul_toBimoduleOne (i : ℤ) (U : Cᵒᵖ) (aa : (A.complex.X i).val.obj U) :
    HEq (((φ.toBimodule hφ).leftMul i 0).app U aa (toBimoduleOne φ hφ U))
      (toBimoduleMap φ hφ i U aa) :=
  B.mul_one i U ((φ.toHomologicalComplex.f i).val.app U aa)

/-- The unit of `B` acts as the identity on the right of the bimodule `{}_A B_B`. -/
theorem heq_rightMul_toBimoduleOne (j : ℤ) (U : Cᵒᵖ)
    (y : ((φ.toBimodule hφ).complex.X j).val.obj U) :
    HEq (((φ.toBimodule hφ).rightMul 0 j).app U (toBimoduleOne φ hφ U)
      (toBimoduleSection φ hφ j U y)) y :=
  B.one_mul j U y

end Spellings

/-! ### The unit `x ↦ x ⊗ 1` -/

namespace DifferentialGradedModule

variable {A B : DifferentialGradedAlgebra.{t, a} R} (φ : A ⟶ B) (hφ : φ.PreservesOne)
  (D : TensorFunctorData.{t, a, m, a, m, v, u} A B (φ.toBimodule hφ))

open DifferentialGradedAlgebra

/-- The map on local sections `x ↦ x ⊗ 1` from a right differential graded `A`-module to its
extension of scalars. -/
def extensionUnitSections (M : DifferentialGradedModule.{t, a, m} A) (i : ℤ) (U : Cᵒᵖ) :
    (M.complex.X i).val.obj U →+ ((D.functor.obj M).complex.X i).val.obj U :=
  AddMonoidHom.mk'
    (fun x => castHom (D.functor.obj M).complex.X (add_zero i) U
      ((D.isTensorProduct M).tmul i 0 U x (toBimoduleOne φ hφ U)))
    (fun x y => by
      rw [(D.isTensorProduct M).tmul_add_left]
      exact map_add _ _ _)

/-- `extensionUnitSections` sends `x` to `x ⊗ 1`, cast to degree `i`. -/
@[simp]
theorem extensionUnitSections_apply (M : DifferentialGradedModule.{t, a, m} A) (i : ℤ)
    (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U) :
    extensionUnitSections φ hφ D M i U x =
      castHom (D.functor.obj M).complex.X (add_zero i) U
        ((D.isTensorProduct M).tmul i 0 U x (toBimoduleOne φ hφ U)) :=
  rfl

/-- The map `x ↦ x ⊗ 1` on local sections is `R`-linear. -/
theorem extensionUnitSections_smul (M : DifferentialGradedModule.{t, a, m} A) (i : ℤ)
    (U : Cᵒᵖ) (r : R.obj.obj U) (x : (M.complex.X i).val.obj U) :
    extensionUnitSections φ hφ D M i U (r • x) =
      r • extensionUnitSections φ hφ D M i U x := by
  simp only [extensionUnitSections_apply]
  rw [(D.isTensorProduct M).tmul_smul_left, castHom_smul]

/-- The map `x ↦ x ⊗ 1` on local sections commutes with restriction along `g : U ⟶ V`. -/
theorem extensionUnitSections_naturality (M : DifferentialGradedModule.{t, a, m} A) (i : ℤ)
    {U V : Cᵒᵖ} (g : U ⟶ V) (x : (M.complex.X i).val.obj U) :
    ((D.functor.obj M).complex.X i).val.map g (extensionUnitSections φ hφ D M i U x) =
      extensionUnitSections φ hφ D M i V ((M.complex.X i).val.map g x) := by
  simp only [extensionUnitSections_apply]
  rw [castHom_naturality, (D.isTensorProduct M).tmul_naturality,
    toBimoduleOne_naturality φ hφ g]
  rfl

/-- The degreewise map of sheaves of modules `x ↦ x ⊗ 1`. -/
def extensionUnitHom (M : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    M.complex.X i ⟶ (D.functor.obj M).complex.X i where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => extensionUnitSections φ hφ D M i U x
          map_add' := fun x y => map_add _ x y
          map_smul' := fun r x => extensionUnitSections_smul φ hφ D M i U r x }
      naturality := fun {_U _V} g => ModuleCat.hom_ext (LinearMap.ext fun x =>
        (extensionUnitSections_naturality φ hφ D M i g x).symm) }

/-- On local sections, `extensionUnitHom` is `extensionUnitSections`. -/
@[simp]
theorem extensionUnitHom_apply (M : DifferentialGradedModule.{t, a, m} A) (i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X i).val.obj U) :
    (extensionUnitHom φ hφ D M i).val.app U x = extensionUnitSections φ hφ D M i U x :=
  rfl

/-- The unit `x ↦ x ⊗ 1` commutes with the differentials, because the unit of `B` is closed:
the second term `(-1)^i x ⊗ d 1` of the signed Leibniz rule vanishes. -/
def extensionUnitComplexHom (M : DifferentialGradedModule.{t, a, m} A) :
    M.complex ⟶ (D.functor.obj M).complex where
  f i := extensionUnitHom φ hφ D M i
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine hom_ext_sections fun U x => ?_
    simp only [homSections_comp]
    simp only [homSections_apply, extensionUnitHom_apply, extensionUnitSections_apply]
    rw [d_castHom_app (D.functor.obj M).complex (add_zero i)
        (show i + 0 + 1 = i + 1 by omega) U,
      (D.isTensorProduct M).tmul_d_castHom i 0 U x (toBimoduleOne φ hφ U),
      toBimoduleOne_d φ hφ U, (D.isTensorProduct M).tmul_zero_right, map_zero, smul_zero,
      add_zero (a := castHom (D.functor.obj M).complex.X (add_right_comm i 1 0) U
        ((D.isTensorProduct M).tmul (i + 1) 0 U
          ((M.complex.d i (i + 1)).val.app U x) (toBimoduleOne φ hφ U))),
      castHom_castHom]

/-- The degree-`i` component of `extensionUnitComplexHom` is `extensionUnitHom`. -/
@[simp]
theorem extensionUnitComplexHom_f (M : DifferentialGradedModule.{t, a, m} A) (i : ℤ) :
    (extensionUnitComplexHom φ hφ D M).f i = extensionUnitHom φ hφ D M i :=
  rfl

/-- The unit `x ↦ x ⊗ 1` is `A`-linear: `x a ⊗ 1 = x ⊗ φ(a) = (x ⊗ 1) φ(a)`. -/
theorem extensionUnitHom_mul (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X n).val.obj U) (aa : (A.complex.X i).val.obj U) :
    (extensionUnitHom φ hφ D M (n + i)).val.app U ((M.mul n i).app U x aa) =
      ((D.functor.obj M).mul n i).app U ((extensionUnitHom φ hφ D M n).val.app U x)
        ((φ.toHomologicalComplex.f i).val.app U aa) := by
  simp only [extensionUnitHom_apply, extensionUnitSections_apply]
  rw [mul_app_castHom (D.functor.obj M) (add_zero n) i U]
  refine castHom_heq _ _ _ _ ?_
  refine HEq.trans
    ((D.isTensorProduct M).tmul_balanced n i 0 U x aa (toBimoduleOne φ hφ U)) ?_
  refine HEq.trans ((D.isTensorProduct M).tmul_heq_right n (show i + 0 = i by omega) U x
    (heq_leftMul_toBimoduleOne φ hφ i U aa)) ?_
  refine HEq.symm (HEq.trans ((D.isTensorProduct M).tmul_rightMul n 0 i U x
    (toBimoduleOne φ hφ U) ((φ.toHomologicalComplex.f i).val.app U aa)) ?_)
  refine (D.isTensorProduct M).tmul_heq_right n (show (0 : ℤ) + i = i by omega) U x ?_
  exact heq_rightMul_toBimoduleOne φ hφ i U (toBimoduleMap φ hφ i U aa)

/-- **The unit of the adjunction**: the homomorphism `x ↦ x ⊗ 1` of right differential graded
`A`-modules from `M` to the restriction of scalars of its extension of scalars. -/
def extensionUnit (M : DifferentialGradedModule.{t, a, m} A) :
    M ⟶ (restriction.{t, a, m} φ hφ).obj (D.functor.obj M) where
  toHomologicalComplex := extensionUnitComplexHom φ hφ D M
  map_mul n i U x aa := extensionUnitHom_mul φ hφ D M n i U x aa

/-- The unit of the adjunction is natural in the right differential graded `A`-module. -/
theorem extensionUnit_naturality {M M' : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ M') :
    f ≫ extensionUnit φ hφ D M' =
      extensionUnit φ hφ D M ≫ (restriction.{t, a, m} φ hφ).map (D.functor.map f) := by
  have key : ∀ (i : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U),
      (extensionUnitHom φ hφ D M' i).val.app U
          ((f.toHomologicalComplex.f i).val.app U x) =
        ((D.functor.map f).toHomologicalComplex.f i).val.app U
          ((extensionUnitHom φ hφ D M i).val.app U x) := by
    intro i U x
    simp only [extensionUnitHom_apply, extensionUnitSections_apply]
    rw [f_app_castHom (D.functor.map f) (add_zero i) U,
      D.map_spec f i 0 U x (toBimoduleOne φ hφ U)]
  exact DifferentialGradedModule.Hom.ext fun i => hom_ext_sections fun U x => key i U x

/-- `x ⊗ y` is the action of `y` on `x ⊗ 1`. -/
theorem castHom_mul_tmul_one {M : DifferentialGradedModule.{t, a, m} A} (i j : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X i).val.obj U)
    (y : ((φ.toBimodule hφ).complex.X j).val.obj U) :
    castHom (D.functor.obj M).complex.X (show i + 0 + j = i + j by omega) U
        (((D.functor.obj M).mul (i + 0) j).app U
          ((D.isTensorProduct M).tmul i 0 U x (toBimoduleOne φ hφ U))
          (toBimoduleSection φ hφ j U y)) =
      (D.isTensorProduct M).tmul i j U x y :=
  eq_of_heq ((heq_castHom (D.functor.obj M).complex.X (show i + 0 + j = i + j by omega) U _).trans
    (((D.isTensorProduct M).tmul_rightMul i 0 j U x (toBimoduleOne φ hφ U)
        (toBimoduleSection φ hφ j U y)).trans
      ((D.isTensorProduct M).tmul_heq_right i (show (0 : ℤ) + j = j by omega) U x
        (heq_rightMul_toBimoduleOne φ hφ j U y))))

/-! ### The inverse bijection -/

variable {M : DifferentialGradedModule.{t, a, m} A} {L : DifferentialGradedModule.{t, a, m} B}

/-- A degreewise component of a homomorphism `M ⟶ res_φ L`, read as a morphism into the
underlying sheaf of modules of `L`. -/
def restrictionHomComponent (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (i : ℤ) :
    M.complex.X i ⟶ L.complex.X i :=
  f.toHomologicalComplex.f i

/-- A degreewise component of `f : M ⟶ res_φ L` satisfies `f (x a) = f (x) φ(a)`. -/
theorem restrictionHomComponent_mul (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X n).val.obj U) (aa : (A.complex.X i).val.obj U) :
    (restrictionHomComponent φ hφ f (n + i)).val.app U ((M.mul n i).app U x aa) =
      (L.mul n i).app U ((restrictionHomComponent φ hφ f n).val.app U x)
        ((φ.toHomologicalComplex.f i).val.app U aa) :=
  f.map_mul n i U x aa

/-- The degreewise components of `f : M ⟶ res_φ L` commute with the differentials on local
sections. -/
theorem restrictionHomComponent_comm (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (i j : ℤ)
    (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U) :
    (L.complex.d i j).val.app U ((restrictionHomComponent φ hφ f i).val.app U x) =
      (restrictionHomComponent φ hφ f j).val.app U ((M.complex.d i j).val.app U x) := by
  have h := homSections_congr (f.toHomologicalComplex.comm i j) U x
  rw [homSections_comp, homSections_comp] at h
  simp only [homSections_apply] at h
  exact h

/-- The biadditive map `(x, b) ↦ f (x) b` on local sections over an object of the slice site,
attached to a homomorphism `f : M ⟶ res_φ L`. -/
def extensionDescendApp (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (i j k : ℤ)
    (hijk : i + j + 0 = k) {U : C} (V : Over U) :
    (M.complex.X i).val.obj (Opposite.op V.left) →+
      ((φ.toBimodule hφ).complex.X j).val.obj (Opposite.op V.left) →+
        (L.complex.X k).val.obj (Opposite.op V.left) :=
  AddMonoidHom.mk'
    (fun x => (castHom L.complex.X (show i + j = k by omega) (Opposite.op V.left)).comp
      (((L.mul i j).app (Opposite.op V.left)
          (homSections (restrictionHomComponent φ hφ f i) (Opposite.op V.left) x)).comp
        (toBimoduleSection φ hφ j (Opposite.op V.left))))
    (fun x x' => AddMonoidHom.ext fun y => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.add_apply, map_add])

/-- `extensionDescendApp` sends `(x, y)` to `f (x) y`, cast to degree `k`. -/
theorem extensionDescendApp_apply (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (i j k : ℤ)
    (hijk : i + j + 0 = k) {U : C} (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : ((φ.toBimodule hφ).complex.X j).val.obj (Opposite.op V.left)) :
    extensionDescendApp φ hφ f i j k hijk V x y =
      castHom L.complex.X (show i + j = k by omega) (Opposite.op V.left)
        ((L.mul i j).app (Opposite.op V.left)
          (homSections (restrictionHomComponent φ hφ f i) (Opposite.op V.left) x)
          (toBimoduleSection φ hφ j (Opposite.op V.left) y)) :=
  rfl

/-- The balanced bilinear family `(x, b) ↦ f (x) b` attached to a homomorphism
`f : M ⟶ res_φ L`. It is balanced because `f (x a) = f (x) φ(a)`, and `B`-linear in the second
variable because the action of `L` is associative. -/
def extensionDescendBalanced (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (U : C) :
    LocalBalancedBilinear M (φ.toBimodule hφ) L 0 U where
  app i j k hijk V := extensionDescendApp φ hφ f i j k hijk V
  map_smul_left i j k hijk V r x y := by
    simp only [extensionDescendApp_apply]
    rw [homSections_smul, (L.mul i j).map_smul_left, castHom_smul]
  map_smul_right i j k hijk V r x y := by
    simp only [extensionDescendApp_apply]
    rw [toBimoduleSection_smul, (L.mul i j).map_smul_right, castHom_smul]
  naturality i j k hijk {V W} q x y := by
    simp only [extensionDescendApp_apply]
    rw [castHom_naturality, (L.mul i j).naturality, homSections_naturality,
      toBimoduleSection_naturality]
    rfl
  balanced i p j k hijk V x aa y := by
    simp only [extensionDescendApp_apply, homSections_apply]
    rw [restrictionHomComponent_mul φ hφ f i p (Opposite.op V.left) x aa,
      toBimoduleSection_leftMul φ hφ p j (Opposite.op V.left) aa y]
    exact castHom_heq _ _ _ _
      (L.mul_assoc i p j (Opposite.op V.left)
        ((restrictionHomComponent φ hφ f i).val.app (Opposite.op V.left) x)
        ((φ.toHomologicalComplex.f p).val.app (Opposite.op V.left) aa)
        (toBimoduleSection φ hφ j (Opposite.op V.left) y))
  map_rightMul i j p k hijk V x y b := by
    simp only [extensionDescendApp_apply, homSections_apply]
    rw [toBimoduleSection_rightMul φ hφ j p (Opposite.op V.left) y b,
      mul_app_castHom L (show i + j = k by omega) p (Opposite.op V.left)]
    exact (castHom_heq _ _ _ _
      (L.mul_assoc i j p (Opposite.op V.left)
        ((restrictionHomComponent φ hφ f i).val.app (Opposite.op V.left) x)
        (toBimoduleSection φ hφ j (Opposite.op V.left) y) b)).symm

/-- The balanced family `extensionDescendBalanced` sends `(x, y)` to `f (x) y`, cast to
degree `k`. -/
theorem extensionDescendBalanced_app (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (U : C)
    (i j k : ℤ) (hijk : i + j + 0 = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : ((φ.toBimodule hφ).complex.X j).val.obj (Opposite.op V.left)) :
    (extensionDescendBalanced φ hφ f U).app i j k hijk V x y =
      castHom L.complex.X (show i + j = k by omega) (Opposite.op V.left)
        ((L.mul i j).app (Opposite.op V.left)
          ((restrictionHomComponent φ hφ f i).val.app (Opposite.op V.left) x)
          (toBimoduleSection φ hφ j (Opposite.op V.left) y)) :=
  extensionDescendApp_apply φ hφ f i j k hijk V x y

/-- The degree-zero local homomorphism `M ⊗_{A, φ} B → L` determined by `x ⊗ b ↦ f (x) b`. -/
def extensionDescendLocalHom (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (U : C) :
    LocalHom (D.functor.obj M) L 0 U :=
  ((D.isTensorProduct M).universal L 0 U).symm (extensionDescendBalanced φ hφ f U)

/-- The balanced family attached to `extensionDescendLocalHom` by the universal property of the
tensor product is `extensionDescendBalanced`. -/
theorem universal_extensionDescendLocalHom (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (U : C) :
    (D.isTensorProduct M).universal L 0 U (extensionDescendLocalHom φ hφ D f U) =
      extensionDescendBalanced φ hφ f U :=
  ((D.isTensorProduct M).universal L 0 U).apply_symm_apply _

/-- The local homomorphism descending `f` sends `x ⊗ y` to `f (x) y`. -/
theorem extensionDescendLocalHom_tmul (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (U : C)
    (i j k : ℤ) (hijk : i + j + 0 = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : ((φ.toBimodule hφ).complex.X j).val.obj (Opposite.op V.left)) :
    (extensionDescendLocalHom φ hφ D f U).app (i + j) k hijk V
        ((D.isTensorProduct M).tmul i j (Opposite.op V.left) x y) =
      castHom L.complex.X (show i + j = k by omega) (Opposite.op V.left)
        ((L.mul i j).app (Opposite.op V.left)
          ((restrictionHomComponent φ hφ f i).val.app (Opposite.op V.left) x)
          (toBimoduleSection φ hφ j (Opposite.op V.left) y)) := by
  have h2 : ((D.isTensorProduct M).universal L 0 U
      (extensionDescendLocalHom φ hφ D f U)).app i j k hijk V x y =
      (extensionDescendBalanced φ hφ f U).app i j k hijk V x y := by
    rw [universal_extensionDescendLocalHom]
  rw [(D.isTensorProduct M).universal_app] at h2
  rw [h2, extensionDescendBalanced_app]

/-- The local homomorphism descending `f` is compatible with restriction along a morphism of
the site. -/
theorem restrict_extensionDescendLocalHom (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) {U U' : C}
    (q : U' ⟶ U) :
    (extensionDescendLocalHom φ hφ D f U).restrict q =
      extensionDescendLocalHom φ hφ D f U' := by
  refine ((D.isTensorProduct M).universal L 0 U').injective
    (LocalBalancedBilinear.ext fun i j k hijk V x y => ?_)
  rw [(D.isTensorProduct M).universal_restrict L 0 q (extensionDescendLocalHom φ hφ D f U)
      i j k hijk V x y,
    universal_extensionDescendLocalHom, universal_extensionDescendLocalHom,
    extensionDescendBalanced_app, extensionDescendBalanced_app]
  rfl

/-- The map on sections over an object of the site given by the local homomorphism descending
`f`. -/
def extensionDescendSections (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (k : ℤ) (U : Cᵒᵖ) :
    ((D.functor.obj M).complex.X k).val.obj U →+ (L.complex.X k).val.obj U :=
  (extensionDescendLocalHom φ hφ D f U.unop).app k k (add_zero k) (Over.mk (𝟙 U.unop))

/-- `extensionDescendSections` is the local homomorphism descending `f`, evaluated at the
identity of `U`. -/
theorem extensionDescendSections_eq (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (k : ℤ) (U : Cᵒᵖ)
    (x : ((D.functor.obj M).complex.X k).val.obj U) :
    extensionDescendSections φ hφ D f k U x =
      (extensionDescendLocalHom φ hφ D f U.unop).app k k (add_zero k)
        (Over.mk (𝟙 U.unop)) x :=
  rfl

/-- The map on sections descending `f` commutes with restriction along `γ : U ⟶ V`. -/
theorem extensionDescendSections_naturality (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (k : ℤ)
    {U V : Cᵒᵖ} (γ : U ⟶ V) (x : ((D.functor.obj M).complex.X k).val.obj U) :
    (L.complex.X k).val.map γ (extensionDescendSections φ hφ D f k U x) =
      extensionDescendSections φ hφ D f k V
        (((D.functor.obj M).complex.X k).val.map γ x) := by
  have hA := (extensionDescendLocalHom φ hφ D f U.unop).naturality k k (add_zero k)
    (Over.homMk γ.unop (Category.comp_id γ.unop) :
      Over.mk γ.unop ⟶ Over.mk (𝟙 U.unop)) x
  refine hA.trans ?_
  refine (LocalGradedHom.app_mk_congr
    (extensionDescendLocalHom φ hφ D f U.unop).toLocalGradedHom k k (add_zero k)
    (Category.id_comp γ.unop).symm (((D.functor.obj M).complex.X k).val.map γ x)).trans ?_
  exact LocalHom.app_congr (restrict_extensionDescendLocalHom φ hφ D f γ.unop) k k (add_zero k)
    (Over.mk (𝟙 V.unop)) (((D.functor.obj M).complex.X k).val.map γ x)

/-- The degreewise map of sheaves of modules descending `f`. -/
def extensionDescendDegHom (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (k : ℤ) :
    (D.functor.obj M).complex.X k ⟶ L.complex.X k where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => extensionDescendSections φ hφ D f k U x
          map_add' := fun x y => map_add _ x y
          map_smul' := fun r x => (extensionDescendLocalHom φ hφ D f U.unop).map_smul k k
            (add_zero k) (Over.mk (𝟙 U.unop)) r x }
      naturality := fun {_U _V} γ => ModuleCat.hom_ext (LinearMap.ext fun x =>
        (extensionDescendSections_naturality φ hφ D f k γ x).symm) }

/-- On local sections, `extensionDescendDegHom` is `extensionDescendSections`. -/
@[simp]
theorem extensionDescendDegHom_apply (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (k : ℤ) (U : Cᵒᵖ)
    (x : ((D.functor.obj M).complex.X k).val.obj U) :
    (extensionDescendDegHom φ hφ D f k).val.app U x =
      extensionDescendSections φ hφ D f k U x :=
  rfl

/-- The degreewise map descending `f` is `B`-linear. -/
theorem extensionDescendDegHom_mul (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (n i : ℤ) (U : Cᵒᵖ)
    (x : ((D.functor.obj M).complex.X n).val.obj U)
    (b : (B.complex.X i).val.obj U) :
    (extensionDescendDegHom φ hφ D f (n + i)).val.app U
        (((D.functor.obj M).mul n i).app U x b) =
      (L.mul n i).app U ((extensionDescendDegHom φ hφ D f n).val.app U x) b :=
  (extensionDescendLocalHom φ hφ D f U.unop).isLinear n n (add_zero n) i
    (Over.mk (𝟙 U.unop)) x b

/-- The local homomorphism descending `f` commutes with the differentials: its defect is a
degree-one local homomorphism killing every `x ⊗ y`, because the signed Leibniz rule for
`M ⊗_{A, φ} B` matches the signed Leibniz rule for `L` once `f` is known to commute with the
differentials. -/
theorem extensionDescendDefect (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (U : C) :
    (extensionDescendLocalHom φ hφ D f U).diffDefect =
      LocalHom.zero (D.functor.obj M) L 1 U := by
  refine (D.isTensorProduct M).localHom_ext fun i j k hijk V x y => ?_
  obtain rfl : i + j + 1 = k := hijk
  rw [LocalHom.zero_app, LocalHom.diffDefect_app,
    extensionDescendLocalHom_tmul φ hφ D f U i j (i + j) (add_zero (i + j)) V x y,
    castHom_self, L.leibniz_castHom i j (Opposite.op V.left) _ _,
    restrictionHomComponent_comm φ hφ f i (i + 1) (Opposite.op V.left) x,
    ← toBimoduleSection_d φ hφ j (j + 1) (Opposite.op V.left) y,
    (D.isTensorProduct M).tmul_d_castHom i j (Opposite.op V.left) x y]
  simp only [map_add, map_zsmul]
  rw [LocalGradedHom.app_castHom_source
      (extensionDescendLocalHom φ hφ D f U).toLocalGradedHom
      (show i + 1 + j = i + j + 1 by omega) (by omega) (by omega) V _,
    LocalGradedHom.app_castHom_source
      (extensionDescendLocalHom φ hφ D f U).toLocalGradedHom
      (show i + (j + 1) = i + j + 1 by omega) (by omega) (by omega) V _,
    extensionDescendLocalHom_tmul φ hφ D f U (i + 1) j (i + j + 1) (by omega) V _ y,
    extensionDescendLocalHom_tmul φ hφ D f U i (j + 1) (i + j + 1) (by omega) V x _]
  abel

/-- The degreewise maps descending `f` commute with the differentials. -/
theorem extensionDescendDegHom_comm (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (i j : ℤ)
    (hij : i + 1 = j) :
    extensionDescendDegHom φ hφ D f i ≫ L.complex.d i j =
      (D.functor.obj M).complex.d i j ≫ extensionDescendDegHom φ hφ D f j := by
  refine hom_ext_sections fun U x => ?_
  have h := LocalHom.app_congr (extensionDescendDefect φ hφ D f U.unop) i j hij
    (Over.mk (𝟙 U.unop)) x
  rw [LocalHom.zero_app] at h
  exact sub_eq_zero.mp h

/-- The morphism of complexes descending `f`. -/
def extensionDescendComplexHom (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) :
    (D.functor.obj M).complex ⟶ L.complex where
  f k := extensionDescendDegHom φ hφ D f k
  comm' i j hij := extensionDescendDegHom_comm φ hφ D f i j hij

/-- **The inverse of the hom-set bijection**: the homomorphism `M ⊗_{A, φ} B ⟶ L` of right
differential graded `B`-modules determined by `x ⊗ b ↦ f (x) b`. -/
def extensionDescendHom (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) : D.functor.obj M ⟶ L where
  toHomologicalComplex := extensionDescendComplexHom φ hφ D f
  map_mul n i U x b := extensionDescendDegHom_mul φ hφ D f n i U x b

/-- The degree-`k` component of `extensionDescendHom` is `extensionDescendDegHom`. -/
@[simp]
theorem extensionDescendHom_f (f : M ⟶ (restriction.{t, a, m} φ hφ).obj L) (k : ℤ) :
    (extensionDescendHom φ hφ D f).toHomologicalComplex.f k =
      extensionDescendDegHom φ hφ D f k :=
  rfl

/-- Composing the unit with a homomorphism out of the extension of scalars sends `x` to
`g (x ⊗ 1)`. -/
theorem restrictionHomComponent_comp_unit (g : D.functor.obj M ⟶ L) (i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X i).val.obj U) :
    (restrictionHomComponent φ hφ
        (extensionUnit φ hφ D M ≫ (restriction.{t, a, m} φ hφ).map g) i).val.app U x =
      (g.toHomologicalComplex.f i).val.app U
        (castHom (D.functor.obj M).complex.X (add_zero i) U
          ((D.isTensorProduct M).tmul i 0 U x (toBimoduleOne φ hφ U))) :=
  rfl

/-! ### The adjunction -/

/-- **The hom-set bijection of the adjunction**
`Hom_{Mod(B, d)}(M ⊗_{A, φ} B, L) ≃ Hom_{Mod(A, d)}(M, res_φ L)`: a homomorphism out of the
extension of scalars is composed with the unit `x ↦ x ⊗ 1`, and a homomorphism
`f : M ⟶ res_φ L` is read as `x ⊗ b ↦ f (x) b`. -/
def extensionRestrictionHomEquiv (M : DifferentialGradedModule.{t, a, m} A)
    (L : DifferentialGradedModule.{t, a, m} B) :
    (D.functor.obj M ⟶ L) ≃ (M ⟶ (restriction.{t, a, m} φ hφ).obj L) where
  toFun g := extensionUnit φ hφ D M ≫ (restriction.{t, a, m} φ hφ).map g
  invFun f := extensionDescendHom φ hφ D f
  left_inv g := by
    have key : ∀ V : C,
        extensionDescendLocalHom φ hφ D
            (extensionUnit φ hφ D M ≫ (restriction.{t, a, m} φ hφ).map g) V =
          LocalHom.ofDgHom g V := by
      intro V
      refine ((D.isTensorProduct M).universal L 0 V).injective
        (LocalBalancedBilinear.ext fun i j k hijk W x y => ?_)
      rw [universal_extensionDescendLocalHom, (D.isTensorProduct M).universal_app,
        extensionDescendBalanced_app, LocalHom.ofDgHom_app,
        restrictionHomComponent_comp_unit,
        f_app_castHom g (add_zero i) (Opposite.op W.left),
        mul_app_castHom L (add_zero i) j (Opposite.op W.left), castHom_castHom,
        ← g.map_mul (i + 0) j (Opposite.op W.left) _ _,
        ← castHom_mul_tmul_one φ hφ D i j (Opposite.op W.left) x y,
        f_app_castHom g (show i + 0 + j = i + j by omega) (Opposite.op W.left),
        castHom_castHom]
    refine DifferentialGradedModule.Hom.ext fun k => ?_
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    have h := LocalHom.app_congr (key U.unop) k k (add_zero k) (Over.mk (𝟙 U.unop)) x
    rw [LocalHom.ofDgHom_app, castHom_self] at h
    exact h
  right_inv f := by
    have key : ∀ (i : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U),
        (extensionDescendDegHom φ hφ D f i).val.app U
            ((extensionUnitHom φ hφ D M i).val.app U x) =
          (restrictionHomComponent φ hφ f i).val.app U x := by
      intro i U x
      have h1 := LocalGradedHom.app_castHom_source
        (extensionDescendLocalHom φ hφ D f U.unop).toLocalGradedHom
        (add_zero i) (show i + 0 + 0 = i by omega) (add_zero i) (Over.mk (𝟙 U.unop))
        ((D.isTensorProduct M).tmul i 0 U x (toBimoduleOne φ hφ U))
      have h2 := extensionDescendLocalHom_tmul φ hφ D f U.unop i 0 i
        (show i + 0 + 0 = i by omega) (Over.mk (𝟙 U.unop)) x (toBimoduleOne φ hφ U)
      have h3 : castHom L.complex.X (show i + 0 = i by omega) U
            ((L.mul i 0).app U ((restrictionHomComponent φ hφ f i).val.app U x)
              (B.one.eval U)) =
          (restrictionHomComponent φ hφ f i).val.app U x :=
        (castHom_heq L.complex.X (show i + 0 = i by omega) (rfl : i = i) U
          (L.mul_one i U ((restrictionHomComponent φ hφ f i).val.app U x))).trans
          (castHom_rfl L.complex.X U _)
      exact (h1.trans h2).trans h3
    exact DifferentialGradedModule.Hom.ext fun i => hom_ext_sections fun U x => key i U x

/-- **Extension of scalars is left adjoint to restriction of scalars.** For a unit-preserving
homomorphism `φ : A ⟶ B` of sheaves of differential graded `R`-algebras and a tensor product
functor `- ⊗_{A, φ} B` with the bimodule `{}_A B_B`, that functor is left adjoint to `res_φ`.
This is the adjunction of [Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP) for an
arbitrary functor whose values are tensor products with `{}_A B_B`; for the tensor product functor
the library constructs it is
`SheafOfModules.DifferentialGradedModule.baseChangeRestrictionAdjunction`. -/
def extensionRestrictionAdjunction : D.functor ⊣ restriction.{t, a, m} φ hφ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M L => extensionRestrictionHomEquiv φ hφ D M L
      homEquiv_naturality_left_symm := fun {M' M L} f g => by
        refine (extensionRestrictionHomEquiv φ hφ D M' L).injective ?_
        rw [Equiv.apply_symm_apply]
        change _ = extensionUnit φ hφ D M' ≫ (restriction.{t, a, m} φ hφ).map
          (D.functor.map f ≫ (extensionRestrictionHomEquiv φ hφ D M L).symm g)
        rw [Functor.map_comp, ← Category.assoc, ← extensionUnit_naturality φ hφ D f,
          Category.assoc]
        change _ = f ≫ extensionRestrictionHomEquiv φ hφ D M L
          ((extensionRestrictionHomEquiv φ hφ D M L).symm g)
        rw [Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {M L L'} g h => by
        change extensionUnit φ hφ D M ≫ (restriction.{t, a, m} φ hφ).map (g ≫ h) =
          (extensionUnit φ hφ D M ≫ (restriction.{t, a, m} φ hφ).map g) ≫
            (restriction.{t, a, m} φ hφ).map h
        rw [Functor.map_comp, Category.assoc] }

end DifferentialGradedModule

end SheafOfModules

end
