module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHom

/-!
# Tensor-hom adjunction for sheaves of differential graded modules

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` and `B` be sheaves of differential
graded `R`-algebras, let `M` be a right differential graded `A`-module, let `N` be a
differential graded `(A, B)`-bimodule and let `L` be a right differential graded `B`-module.
Writing `T` for the tensor product `M ⊗_A N`, a right differential graded `B`-module, and `H`
for the internal hom `SheafHom^dg_B(N, L)`, a right differential graded `A`-module, the source
states the two displayed identities

`Hom_{Mod^dg(B, d)}(M ⊗_A N, L) = Hom_{Mod^dg(A, d)}(M, SheafHom^dg_B(N, L))`

and

`SheafHom^dg_B(M ⊗_A N, L) = SheafHom^dg_A(M, SheafHom^dg_B(N, L))`.

This file proves the second of the two. Both come from reading each side as the `A`-balanced
bilinear maps `M × N → L` which are `B`-linear on the right, by
`φ ↦ (x ↦ (y ↦ φ (x ⊗ y)))`, and the differential graded content is that this reading is
compatible with the differentials. That compatibility is sign-free: for a degree-`n`
homomorphism `φ` out of `M ⊗_A N`, with `x` of degree `i` and `y` of degree `j`,

`(d φ)(x ⊗ y) = d (φ (x ⊗ y)) - (-1)^n φ (d x ⊗ y) - (-1)^{n + i} φ (x ⊗ d y)`

is also what `d` of the corresponding homomorphism `M → SheafHom^dg_B(N, L)` does to `x` and
`y`, because the sign `(-1)^{n + i}` produced by the differential of the internal hom in degree
`i + n` is the sign `(-1)^n (-1)^i` produced by the Leibniz rule for `d (x ⊗ y)`.

## Main definitions

* `SheafOfModules.balancedEquivDg` identifies the degree-`n` local homomorphisms
  `M|_U → SheafHom^dg_B(N, L)|_U` of right differential graded `A`-modules with the
  `A`-balanced bilinear families of degree `n` over `U`. `SheafOfModules.toBalancedDg` and
  `SheafOfModules.ofBalancedDg` are its two directions, `SheafOfModules.balancedValDg` the
  value of the family attached to a local homomorphism, and `SheafOfModules.balancedHomDg` the
  local homomorphism `N|_V → L|_V` that a balanced bilinear family attaches to a local section
  of `M`.
* `SheafOfModules.tensorSectionsEquiv` is the identification of the sections of
  `SheafHom^dg_B(M ⊗_A N, L)` with the local homomorphisms `M → SheafHom^dg_B(N, L)` which the
  second identity consists of.

## Main results

* `SheafOfModules.IsSheafHom.mul_spec_top` evaluates the right `A`-action on
  `SheafHom^dg_B(N, L)` over the base of a slice site, where no scalar restriction intervenes.
* `SheafOfModules.isInternalHom_tensor` is the second displayed identity: a complex of sheaves
  of `R`-modules which is the internal hom `SheafHom^dg_B(M ⊗_A N, L)` is also the internal hom
  `SheafHom^dg_A(M, SheafHom^dg_B(N, L))`, differentials included.
* `SheafOfModules.tensorSectionsEquiv_eval` and `SheafOfModules.tensorSectionsEquiv_d` are its
  two halves: the identification is `φ ↦ (x ↦ (y ↦ φ (x ⊗ y)))`, and it is compatible with the
  differentials.
* `SheafOfModules.tensorSectionsEquiv_naturality_left`,
  `SheafOfModules.tensorSectionsEquiv_naturality_right` and
  `SheafOfModules.tensorSectionsEquiv_naturality_bimodule` are the source's functoriality of the
  second identity in `M`, in `L` and in `N`.
* `SheafOfModules.ofBalancedDg_toBalancedDg` and `SheafOfModules.toBalancedDg_ofBalancedDg`: the
  local identification of local homomorphisms into the internal hom with balanced bilinear
  families is a bijection, and `SheafOfModules.toBalancedDg_restrict`,
  `SheafOfModules.ofBalancedDg_restrict`: it is compatible with restriction along a morphism of
  the site.

## Implementation notes

Neither the tensor product nor the internal hom can be written down by a formula over a general
ringed site, so both are used through the predicates `SheafOfModules.IsTensorProduct` and
`SheafOfModules.IsInternalHom`, which pin them up to canonical isomorphism; see the
implementation notes of the two files where those are defined. Accordingly the identity is
stated for an arbitrary `T` which *is* `M ⊗_A N` and an arbitrary `H` which *is*
`SheafHom^dg_B(N, L)`.

The right differential graded `A`-module `SheafHom^dg_B(N, L)` is used through
`SheafOfModules.IsSheafHom` and the right differential graded `B`-module underlying the
bimodule through `SheafOfModules.DifferentialGradedBimodule.toRightModule`, both of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforwardHom.lean`, rather
than redeclared here; `IsSheafHom.mul_spec` is the right `A`-action `(f a)(y) = f (a y)`, which
involves no signs.

The identity is stated as a transfer of the predicate rather than as an isomorphism of
complexes: a complex of sheaves of `R`-modules which is the one internal hom is also the other.
That is the content of the source's equality of two internal homs, and it avoids choosing one
of the two as a representative. This is the device used for the undifferentiated identity in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedTensorHomAdjunction.lean`, of which the
material below is the differential analogue.

The first displayed identity is proved not here but in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensorHomHomComplex.lean`, as
`SheafOfModules.DifferentialGradedModule.homogeneousEquiv` with its additivity and its
compatibility with the differentials, and as
`SheafOfModules.DifferentialGradedModule.dgHomEquiv` and
`SheafOfModules.DifferentialGradedModule.dgHomEquiv_d` inside the differential graded
categories; those five declarations carry the `@[stacks 0FRS ...]` clauses for it, and the
attribute below is the suffixed form naming only the second identity. That proof runs on the
local material of this file: the homogeneous morphisms of the differential
graded categories `Mod^dg(B, d)` and `Mod^dg(A, d)` are the action-linear cochains
`SheafOfModules.DifferentialGradedModule.HomogeneousMap` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAxiomA.lean`, whose differential
is the commutator `d(f) = d_L ∘ f - (-1)^n f ∘ d_M`, and such a cochain is the same datum as a
compatible family of the local homomorphisms used below.

`M` and `H` are taken in one module universe, as in the undifferentiated file; the universes of
the site, the sheaf of rings, the algebras, the bimodule `N`, the modules `L` and `T` and the
complex `G` are otherwise independent. The base is an arbitrary sheaf of rings on an arbitrary
site rather than the structure sheaf of a ringed site; a ringed site `X` is the case
`R := X.ringSheaf`.

The source's `functorially in M, N, L` is the naturality section at the end of the file. The
identification it is about is `SheafOfModules.tensorSectionsEquiv`, which is by definition the
`sectionsEquiv` field of `SheafOfModules.isInternalHom_tensor`. A morphism between the objects
the source's statement names induces one between the tensor products and one between the
internal homs, and the three theorems say that one induced morphism of internal homs is
simultaneously the one attached to the `M ⊗_A N` side and the one attached to the
`SheafHom^dg_A(M, -)` side; that is the content of functoriality for an identity which is an
equality of objects rather than a chosen isomorphism. Because none of those induced morphisms
can be written by a formula over a general ringed site any more than the objects can, each is
taken as a morphism together with the hypothesis pinning it on local sections, in the same way
as the objects are taken with the predicates that pin them. Those hypotheses are realized and
restrict nothing: the `ht` of `SheafOfModules.tensorSectionsEquiv_naturality_left` is
`SheafOfModules.TensorFunctorData.map_spec`, the `hg` of
`SheafOfModules.tensorSectionsEquiv_naturality_right` is
`SheafOfModules.SheafHomFunctorData.map_spec`, and each `hα` is
`SheafOfModules.InternalHomFunctorData.map_spec` for the pair of morphisms in question, with the
identity in the variable that does not move; the remaining two, the morphism of tensor products
and the morphism of internal homs induced by a morphism of the bimodule, have the same shape and
are determined by the `sectionsEquiv` and `universal` data of the predicates, but no carrier for
them is declared in this library, so they too are taken as hypotheses here.

## References

* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 0FR6](https://stacks.math.columbia.edu/tag/0FR6)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
-/

@[expose] public section

open CategoryTheory

universe t a w z s g v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R}

/-! ### Two values of a local homomorphism on heterogeneously equal sections -/

/-- Two values of a degree-`n` map of the underlying graded modules on heterogeneously equal
local sections of the source agree. -/
theorem LocalGradedHom.app_congr_heq {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L : DifferentialGradedModule.{t, a, z} A'}
    {n : ℤ} {U : C} (f : LocalGradedHom K L n U) {i i' j : ℤ} (hij : i + n = j)
    (hij' : i' + n = j) (V : Over U)
    {x : (K.complex.X i).val.obj (Opposite.op V.left)}
    {y : (K.complex.X i').val.obj (Opposite.op V.left)} (hxy : HEq x y) :
    f.app i j hij V x = f.app i' j hij' V y := by
  obtain rfl : i = i' := by omega
  obtain rfl := eq_of_heq hxy
  rfl

/-- The value on local sections of the differential of the internal hom, computed through
arbitrary presentations of the two intermediate degrees. -/
theorem localDiffApp_eq {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L' : DifferentialGradedModule.{t, a, z} A'}
    {n : ℤ} {U : C} (f : LocalGradedHom K L' n U) (m i j q r : ℤ) (hij : i + m = j)
    (hq : i + n = q) (hr : i + m - n = r) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    localDiffApp f m i j hij V x =
      (L'.complex.d q j).val.app (Opposite.op V.left) (f.app i q hq V x) +
        (Int.negOnePow m : ℤ) • f.app r j (by omega) V
          ((K.complex.d i r).val.app (Opposite.op V.left) x) := by
  subst hq
  subst hr
  rfl

/-- The differential of the internal hom vanishes outside the degrees where the differentials
of the source and the target do. -/
theorem localDiffApp_of_ne {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L' : DifferentialGradedModule.{t, a, z} A'}
    {n : ℤ} {U : C} (f : LocalGradedHom K L' n U) (m i j : ℤ) (hij : i + m = j)
    (hm : m ≠ n + 1) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    localDiffApp f m i j hij V x = 0 := by
  have h1 : ¬(i + n + 1 = j) := by omega
  have h2 : ¬(i + 1 = i + m - n) := by omega
  have e1 : (L'.complex.d (i + n) j).val.app (Opposite.op V.left)
      (f.app i (i + n) rfl V x) = 0 := by
    rw [L'.complex.shape (i + n) j h1]
    rfl
  have e2 : (K.complex.d i (i + m - n)).val.app (Opposite.op V.left) x = 0 := by
    rw [K.complex.shape i (i + m - n) h2]
    rfl
  rw [localDiffApp_eq f m i j (i + n) (i + m - n) hij rfl rfl V x, e1, e2, map_zero,
    smul_zero, add_zero]

/-- A degree-`n` map of the underlying graded modules absorbs a transport of the degree of its
argument. -/
theorem LocalGradedHom.app_castHom_src {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L' : DifferentialGradedModule.{t, a, z} A'}
    {n : ℤ} {U : C} (f : LocalGradedHom K L' n U) {i i' j : ℤ} (h : i = i') (hij : i' + n = j)
    (V : Over U) (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    f.app i' j hij V (castHom K.complex.X h (Opposite.op V.left) x) =
      f.app i j (by omega) V x := by
  subst h
  rfl

/-! ### Naming a local homomorphism by a section of the internal hom -/

namespace IsInternalHom

variable {M : DifferentialGradedModule.{t, a, w} A} {L : DifferentialGradedModule.{t, a, z} A}
  {H : CochainComplex (SheafOfModules.{s} R) ℤ}

/-- Naming a local homomorphism by a section of the internal hom is additive. -/
theorem symm_add (hH : IsInternalHom M L H) (n : ℤ) (U : C)
    (p q r : LocalHom M L n U)
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)),
      r.app i j hij V x = p.app i j hij V x + q.app i j hij V x) :
    (hH.sectionsEquiv n U).symm r =
      (hH.sectionsEquiv n U).symm p + (hH.sectionsEquiv n U).symm q := by
  refine (hH.sectionsEquiv n U).injective (LocalHom.ext fun i j hij V x => ?_)
  rw [hH.sectionsEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact h i j hij V x

/-- Naming a local homomorphism by a section of the internal hom is linear over the sheaf of
rings. -/
theorem symm_smul (hH : IsInternalHom M L H) (n : ℤ) (U : C) (r : R.obj.obj (Opposite.op U))
    (p q : LocalHom M L n U)
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left)),
      q.app i j hij V x = R.obj.map V.hom.op r • p.app i j hij V x) :
    (hH.sectionsEquiv n U).symm q = r • (hH.sectionsEquiv n U).symm p := by
  refine (hH.sectionsEquiv n U).injective (LocalHom.ext fun i j hij V x => ?_)
  rw [hH.sectionsEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h i j hij V x

/-- Naming a local homomorphism by a section of the internal hom is compatible with restriction
along a morphism of the site. -/
theorem symm_naturality (hH : IsInternalHom M L H) (n : ℤ) {U U' : C} (g : U' ⟶ U)
    (p : LocalHom M L n U) :
    (hH.sectionsEquiv n U').symm (p.restrict g) =
      (H.X n).val.map g.op ((hH.sectionsEquiv n U).symm p) := by
  refine (hH.sectionsEquiv n U').injective (LocalHom.ext fun i j hij V x => ?_)
  rw [Equiv.apply_symm_apply, hH.sectionsEquiv_naturality n g, Equiv.apply_symm_apply]
  rfl

/-- The identification of sections of the internal hom with local homomorphisms is compatible
with integer multiples. -/
theorem sectionsEquiv_zsmul (hH : IsInternalHom M L H) (n : ℤ) (U : C) (r : ℤ)
    (p : (H.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (hH.sectionsEquiv n U (r • p)).app i j hij V x =
      r • (hH.sectionsEquiv n U p).app i j hij V x :=
  map_zsmul
    ({ toFun := fun q => (hH.sectionsEquiv n U q).app i j hij V x
       map_zero' := hH.sectionsEquiv_zero n U i j hij V x
       map_add' := fun q q' => hH.sectionsEquiv_add n U q q' i j hij V x } :
      (H.X n).val.obj (Opposite.op U) →+ (L.complex.X j).val.obj (Opposite.op V.left)) r p

/-- The degree-`n` sections of the internal hom over `U` act on sections over `U` itself
without a scalar restriction. -/
theorem sectionsEquiv_smul_top (hH : IsInternalHom M L H) (n : ℤ) (U : C)
    (r : R.obj.obj (Opposite.op U)) (p : (H.X n).val.obj (Opposite.op U)) (i j : ℤ)
    (hij : i + n = j) (x : (M.complex.X i).val.obj (Opposite.op U)) :
    (hH.sectionsEquiv n U (r • p)).app i j hij (Over.mk (𝟙 U)) x =
      r • (hH.sectionsEquiv n U p).app i j hij (Over.mk (𝟙 U)) x := by
  rw [hH.sectionsEquiv_smul, ring_map_top]

/-- The value at the identity of `U'` of the local homomorphism named by the restriction of a
section along `g : U' ⟶ U` is the value of the local homomorphism named by the section at `g`. -/
private theorem sectionsEquiv_map_top (hH : IsInternalHom M L H) (n : ℤ) {U U' : C} (g : U' ⟶ U)
    (p : (H.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
    (x : (M.complex.X i).val.obj (Opposite.op U')) :
    (hH.sectionsEquiv n U' ((H.X n).val.map g.op p)).app i j hij (Over.mk (𝟙 U')) x =
      (hH.sectionsEquiv n U p).app i j hij (Over.mk g) x := by
  rw [hH.sectionsEquiv_naturality n g]
  exact (hH.sectionsEquiv n U p).toLocalGradedHom.app_mk_congr i j hij (Category.id_comp g) x

end IsInternalHom

namespace IsSheafHom

variable {N : DifferentialGradedBimodule.{t, a, z} A B} {L : DifferentialGradedModule.{t, a, s} B}
  {H : DifferentialGradedModule.{t, a, w} A}

/-- The right `A`-action on the internal hom, evaluated on sections over the base of the slice
site, where no scalar restriction intervenes. -/
theorem mul_spec_top (hH : IsSheafHom N L H) (n m : ℤ) (U : C)
    (p : (H.complex.X n).val.obj (Opposite.op U))
    (b : (A.complex.X m).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + (n + m) = j)
    (y : (N.complex.X i).val.obj (Opposite.op U)) :
    (hH.isInternalHom.sectionsEquiv (n + m) U
        ((H.mul n m).app (Opposite.op U) p b)).app i j hij (Over.mk (𝟙 U)) y =
      (hH.isInternalHom.sectionsEquiv n U p).app (m + i) j (by omega) (Over.mk (𝟙 U))
        ((N.leftMul m i).app (Opposite.op U) b y) := by
  rw [hH.mul_spec n m U p b i j hij (Over.mk (𝟙 U)) y, map_top_sections]
  rfl

end IsSheafHom

/-! ### Restriction of a balanced bilinear family -/

namespace LocalBalancedBilinear

variable {M : DifferentialGradedModule.{t, a, w} A}
  {N : DifferentialGradedBimodule.{t, a, z} A B} {L : DifferentialGradedModule.{t, a, s} B}

/-- The value of a balanced bilinear family over an object of the slice site depends only on
the structure morphism of that object. -/
theorem app_mk_congr {n : ℤ} {U U' : C} (β : LocalBalancedBilinear M N L n U) (i j k : ℤ)
    (hijk : i + j + n = k) {g g' : U' ⟶ U} (hg : g = g')
    (x : (M.complex.X i).val.obj (Opposite.op U'))
    (y : (N.complex.X j).val.obj (Opposite.op U')) :
    β.app i j k hijk (Over.mk g) x y = β.app i j k hijk (Over.mk g') x y := by
  subst hg
  rfl

/-- A balanced bilinear family evaluated over the terminal object of a slice site is its value
over the base. -/
theorem app_top {n : ℤ} {U : C} (β : LocalBalancedBilinear M N L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    β.app i j k hijk (Over.mk ((Over.mk (𝟙 V.left)).hom ≫ V.hom))
        ((M.complex.X i).val.map (Over.mk (𝟙 V.left)).hom.op x) y =
      β.app i j k hijk V x y :=
  (congrArg (fun u : (N.complex.X j).val.obj (Opposite.op V.left) =>
      β.app i j k hijk (Over.mk ((Over.mk (𝟙 V.left)).hom ≫ V.hom))
        ((M.complex.X i).val.map (Over.mk (𝟙 V.left)).hom.op x) u)
    (map_top_sections (N.complex.X j) V.left y).symm).trans
      ((β.naturality i j k hijk
        (Over.homMk (𝟙 V.left) rfl :
          Over.mk ((Over.mk (𝟙 V.left)).hom ≫ V.hom) ⟶ V) x y).symm.trans
          (map_top_sections (L.complex.X k) V.left _))

/-- Restrict a balanced bilinear family along a morphism `U' ⟶ U` of the site, by viewing the
objects of the slice site over `U'` as objects over `U`. -/
def restrict {n : ℤ} {U U' : C} (g : U' ⟶ U) (β : LocalBalancedBilinear M N L n U) :
    LocalBalancedBilinear M N L n U' where
  app i j k hijk V := β.app i j k hijk (Over.mk (V.hom ≫ g))
  map_smul_left i j k hijk V r x y :=
    β.map_smul_left i j k hijk (Over.mk (V.hom ≫ g)) r x y
  map_smul_right i j k hijk V r x y :=
    β.map_smul_right i j k hijk (Over.mk (V.hom ≫ g)) r x y
  naturality i j k hijk {V W} q x y :=
    β.naturality i j k hijk (V := Over.mk (V.hom ≫ g)) (W := Over.mk (W.hom ≫ g))
      (Over.homMk q.left (show q.left ≫ V.hom ≫ g = W.hom ≫ g by
        rw [← Category.assoc, Over.w q])) x y
  balanced i p j k hijk V x b y := β.balanced i p j k hijk (Over.mk (V.hom ≫ g)) x b y
  map_rightMul i j p k hijk V x y b :=
    β.map_rightMul i j p k hijk (Over.mk (V.hom ≫ g)) x y b

/-- The value of the restriction of a balanced bilinear family along `g : U' ⟶ U` at an object
`V` over `U'` is the value of the original family at `V`, viewed as an object over `U`. -/
@[simp]
theorem restrict_app {n : ℤ} {U U' : C} (g : U' ⟶ U) (β : LocalBalancedBilinear M N L n U)
    (i j k : ℤ) (hijk : i + j + n = k) (V : Over U')
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (β.restrict g).app i j k hijk V x y = β.app i j k hijk (Over.mk (V.hom ≫ g)) x y := rfl

end LocalBalancedBilinear

/-- The inverse of the universal bijection of a tensor product is compatible with restriction
along a morphism of the site. -/
theorem IsTensorProduct.universal_symm_restrict {M : DifferentialGradedModule.{t, a, w} A}
    {N : DifferentialGradedBimodule.{t, a, z} A B} {T : DifferentialGradedModule.{t, a, s} B}
    (hT : IsTensorProduct M N T) (L : DifferentialGradedModule.{t, a, s} B) (n : ℤ)
    {U U' : C} (g : U' ⟶ U) (β : LocalBalancedBilinear M N L n U) :
    ((hT.universal L n U).symm β).restrict g = (hT.universal L n U').symm (β.restrict g) := by
  refine (hT.universal L n U').injective (LocalBalancedBilinear.ext fun i j k hijk V x y => ?_)
  rw [hT.universal_restrict L n g ((hT.universal L n U).symm β) i j k hijk V x y,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, LocalBalancedBilinear.restrict_app]

section LocalAdjunction

variable {M H : DifferentialGradedModule.{t, a, w} A}
  {N : DifferentialGradedBimodule.{t, a, z} A B} {L : DifferentialGradedModule.{t, a, s} B}
  {n : ℤ}

/-! ### From a local homomorphism into the internal hom to a balanced bilinear family -/

/-- The value on a local section of `M^i` of the `A`-balanced bilinear family attached to a
degree-`n` local homomorphism `M|_U → SheafHom^dg_B(N, L)|_U`: it sends `(x, y)` to the value
at `y` of the local homomorphism `f (x)`. -/
noncomputable def balancedValDg (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k)
    (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (N.complex.X j).val.obj (Opposite.op V.left) →+
      (L.complex.X k).val.obj (Opposite.op V.left) :=
  (hH.isInternalHom.sectionsEquiv m V.left (f.app i m him V x)).app j k hjk (Over.mk (𝟙 V.left))

/-- The value of `balancedValDg hH f` at `x` is the value at the identity of `V.left` of the
local homomorphism named by the section `f (x)` of the internal hom. -/
theorem balancedValDg_eq (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    balancedValDg hH f i j k m him hjk V x =
      (hH.isInternalHom.sectionsEquiv m V.left (f.app i m him V x)).app j k hjk
        (Over.mk (𝟙 V.left)) := rfl

/-- The intermediate degree in the value of a balanced bilinear family is determined by the
other two, so any proof of its defining equation gives the same value. -/
theorem balancedValDg_congr (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) (i j k m m' : ℤ) (him : i + n = m) (him' : i + n = m')
    (hjk : j + m = k) (hjk' : j + m' = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    balancedValDg hH f i j k m him hjk V x y =
      balancedValDg hH f i j k m' him' hjk' V x y := by
  obtain rfl : m = m' := by omega
  rfl

/-- The value of `balancedValDg hH f` is additive in the section of `M`. -/
theorem balancedValDg_add (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k)
    (V : Over U) (x x' : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    balancedValDg hH f i j k m him hjk V (x + x') y =
      balancedValDg hH f i j k m him hjk V x y +
        balancedValDg hH f i j k m him hjk V x' y := by
  rw [balancedValDg_eq, balancedValDg_eq, balancedValDg_eq,
    show f.app i m him V (x + x') = f.app i m him V x + f.app i m him V x' from map_add _ _ _]
  exact hH.isInternalHom.sectionsEquiv_add m V.left _ _ j k hjk (Over.mk (𝟙 V.left)) y

/-- The value of `balancedValDg hH f` is linear over `R` in the section of `M`. -/
theorem balancedValDg_smul (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k)
    (V : Over U) (r : R.obj.obj (Opposite.op V.left))
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    balancedValDg hH f i j k m him hjk V (r • x) y =
      r • balancedValDg hH f i j k m him hjk V x y := by
  rw [balancedValDg_eq, balancedValDg_eq,
    show f.app i m him V (r • x) = r • f.app i m him V x from f.map_smul i m him V r x]
  exact hH.isInternalHom.sectionsEquiv_smul_top m V.left r _ j k hjk y

/-- The value of `balancedValDg hH f` commutes with restriction along a morphism `W ⟶ V` of
objects over `U`. -/
theorem balancedValDg_naturality (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k)
    {V W : Over U} (q : W ⟶ V) (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (L.complex.X k).val.map q.left.op (balancedValDg hH f i j k m him hjk V x y) =
      balancedValDg hH f i j k m him hjk W ((M.complex.X i).val.map q.left.op x)
        ((N.complex.X j).val.map q.left.op y) := by
  have hW : balancedValDg hH f i j k m him hjk W ((M.complex.X i).val.map q.left.op x) =
      (hH.isInternalHom.sectionsEquiv m W.left
        (f.app i m him W ((M.complex.X i).val.map q.left.op x))).app j k hjk
        (Over.mk (𝟙 W.left)) := rfl
  rw [balancedValDg_eq, hW]
  refine ((hH.isInternalHom.sectionsEquiv m V.left (f.app i m him V x)).naturality j k hjk
    (Over.homMk q.left (Category.comp_id q.left) :
      Over.mk q.left ⟶ Over.mk (𝟙 V.left)) y).trans ?_
  refine (hH.isInternalHom.sectionsEquiv_map_top m q.left (f.app i m him V x) j k hjk
    ((N.complex.X j).val.map q.left.op y)).symm.trans ?_
  exact congrArg (fun pp : (H.complex.X m).val.obj (Opposite.op W.left) =>
    (hH.isInternalHom.sectionsEquiv m W.left pp).app j k hjk (Over.mk (𝟙 W.left))
      ((N.complex.X j).val.map q.left.op y)) (f.naturality i m him q x)

/-- The `A`-balanced bilinear family of degree `n` attached to a degree-`n` local homomorphism
`M|_U → SheafHom^dg_B(N, L)|_U` of right differential graded `A`-modules. -/
noncomputable def toBalancedDg (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) : LocalBalancedBilinear M N L n U where
  app i j k hijk V := AddMonoidHom.mk'
    (fun x => balancedValDg hH f i j k (i + n) rfl (by omega) V x)
    (fun x x' => AddMonoidHom.ext fun y =>
      balancedValDg_add hH f i j k (i + n) rfl (by omega) V x x' y)
  map_smul_left i j k hijk V r x y :=
    balancedValDg_smul hH f i j k (i + n) rfl (by omega) V r x y
  map_smul_right i j k hijk V r x y :=
    (hH.isInternalHom.sectionsEquiv (i + n) V.left
      (f.app i (i + n) rfl V x)).map_smul j k (by omega) (Over.mk (𝟙 V.left)) r y
  naturality i j k hijk {V W} q x y :=
    balancedValDg_naturality hH f i j k (i + n) rfl (by omega) q x y
  balanced i p j k hijk V x b y := by
    refine (balancedValDg_congr hH f (i + p) j k (i + p + n) (i + n + p) rfl (by omega)
      (by omega) (by omega) V _ y).trans ?_
    refine Eq.trans ?_ (hH.mul_spec_top (i + n) p V.left (f.app i (i + n) rfl V x) b
      j k (by omega) y)
    exact congrArg (fun pp : (H.complex.X (i + n + p)).val.obj (Opposite.op V.left) =>
      (hH.isInternalHom.sectionsEquiv (i + n + p) V.left pp).app j k (by omega)
        (Over.mk (𝟙 V.left)) y)
      (f.isLinear i (i + n) rfl p V x b)
  map_rightMul i j p k hijk V x y b :=
    (hH.isInternalHom.sectionsEquiv (i + n) V.left
      (f.app i (i + n) rfl V x)).isLinear j k (by omega) p (Over.mk (𝟙 V.left)) y b

/-- The components of `toBalancedDg hH f` are given by `balancedValDg hH f`. -/
theorem toBalancedDg_app (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (toBalancedDg hH f).app i j k hijk V x =
      balancedValDg hH f i j k (i + n) rfl (by omega) V x := rfl

/-! ### From a balanced bilinear family to a local homomorphism into the internal hom -/

/-- The local homomorphism `N|_{V.left} → L|_{V.left}` of right differential graded `B`-modules
of degree `j` that an `A`-balanced bilinear family of degree `n` attaches to a local section `x`
of `M^i`, where `i + n = j`. It sends `y` to the value of the family on `(x, y)`. -/
noncomputable def balancedHomDg {U : C} (β : LocalBalancedBilinear M N L n U) {i j : ℤ}
    (hij : i + n = j) (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    LocalHom N.toRightModule L j V.left where
  app j' k hj'k W := β.app i j' k (by omega) (Over.mk (W.hom ≫ V.hom))
    ((M.complex.X i).val.map W.hom.op x)
  map_smul j' k hj'k W r y :=
    β.map_smul_right i j' k (by omega) (Over.mk (W.hom ≫ V.hom)) r _ y
  naturality j' k hj'k {W₁ W₂} q y := by
    have hw : q.left ≫ (Over.mk (W₁.hom ≫ V.hom)).hom = (Over.mk (W₂.hom ≫ V.hom)).hom := by
      change q.left ≫ W₁.hom ≫ V.hom = W₂.hom ≫ V.hom
      rw [← Category.assoc, Over.w q]
    have hmx : (M.complex.X i).val.map q.left.op ((M.complex.X i).val.map W₁.hom.op x) =
        (M.complex.X i).val.map W₂.hom.op x := by
      rw [← (M.complex.X i).val.map_comp_apply, ← op_comp, Over.w q]
    refine (β.naturality i j' k (by omega)
      (Over.homMk q.left hw :
        Over.mk (W₂.hom ≫ V.hom) ⟶ Over.mk (W₁.hom ≫ V.hom)) _ y).trans ?_
    exact congrArg (fun v : (M.complex.X i).val.obj (Opposite.op W₂.left) =>
      β.app i j' k (by omega) (Over.mk (W₂.hom ≫ V.hom)) v
        ((N.complex.X j').val.map q.left.op y)) hmx
  isLinear j' k hj'k p W y b :=
    β.map_rightMul i j' p k (by omega) (Over.mk (W.hom ≫ V.hom)) _ y b

/-- The value of `balancedHomDg β hij V x` at an object `W` over `V.left` is the value of `β`
at `W`, viewed as an object over `U`, on the restriction of `x` to `W`. -/
theorem balancedHomDg_eq {U : C} (β : LocalBalancedBilinear M N L n U) {i j : ℤ}
    (hij : i + n = j) (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (j' k : ℤ) (hj'k : j' + j = k) (W : Over V.left) :
    (balancedHomDg β hij V x).app j' k hj'k W =
      β.app i j' k (by omega) (Over.mk (W.hom ≫ V.hom))
        ((M.complex.X i).val.map W.hom.op x) := rfl

/-- The degree-`n` local homomorphism `M|_U → SheafHom^dg_B(N, L)|_U` of right differential
graded `A`-modules attached to an `A`-balanced bilinear family of degree `n` over `U`. -/
noncomputable def ofBalancedDg (hH : IsSheafHom N L H) {U : C}
    (β : LocalBalancedBilinear M N L n U) : LocalHom M H n U where
  app i j hij V := AddMonoidHom.mk'
    (fun x => (hH.isInternalHom.sectionsEquiv j V.left).symm (balancedHomDg β hij V x))
    (fun x x' => hH.isInternalHom.symm_add j V.left _ _ _ fun j' k hj'k W y => by
      rw [balancedHomDg_eq, balancedHomDg_eq, balancedHomDg_eq,
        show (M.complex.X i).val.map W.hom.op (x + x') =
            (M.complex.X i).val.map W.hom.op x + (M.complex.X i).val.map W.hom.op x' from
          map_add _ _ _]
      exact DFunLike.congr_fun (map_add (β.app i j' k (by omega)
        (Over.mk (W.hom ≫ V.hom))) _ _) y)
  map_smul i j hij V r x :=
    hH.isInternalHom.symm_smul j V.left r _ _ fun j' k hj'k W y => by
      rw [balancedHomDg_eq, balancedHomDg_eq,
        show (M.complex.X i).val.map W.hom.op (r • x) =
            R.obj.map W.hom.op r • (M.complex.X i).val.map W.hom.op x from
          PresheafOfModules.map_smul _ _ _ _]
      exact β.map_smul_left i j' k (by omega) (Over.mk (W.hom ≫ V.hom)) _ _ y
  naturality i j hij {V W} q x := by
    have hres : (balancedHomDg β hij V x).restrict q.left =
        balancedHomDg β hij W ((M.complex.X i).val.map q.left.op x) := by
      refine LocalHom.ext fun j' k hj'k W' y => ?_
      have hov : (W'.hom ≫ q.left) ≫ V.hom = W'.hom ≫ W.hom := by
        rw [Category.assoc, Over.w q]
      have hsec : (M.complex.X i).val.map (W'.hom ≫ q.left).op x =
          (M.complex.X i).val.map W'.hom.op ((M.complex.X i).val.map q.left.op x) := by
        rw [op_comp, (M.complex.X i).val.map_comp_apply]
      have hl : ((balancedHomDg β hij V x).restrict q.left).app j' k hj'k W' y =
          β.app i j' k (by omega) (Over.mk ((W'.hom ≫ q.left) ≫ V.hom))
            ((M.complex.X i).val.map (W'.hom ≫ q.left).op x) y := rfl
      have hr : (balancedHomDg β hij W ((M.complex.X i).val.map q.left.op x)).app j' k hj'k W'
            y =
          β.app i j' k (by omega) (Over.mk (W'.hom ≫ W.hom))
            ((M.complex.X i).val.map W'.hom.op
              ((M.complex.X i).val.map q.left.op x)) y := rfl
      refine hl.trans (Eq.trans ?_ hr.symm)
      refine (β.app_mk_congr i j' k (by omega) hov _ y).trans ?_
      exact congrArg (fun v : (M.complex.X i).val.obj (Opposite.op W'.left) =>
        β.app i j' k (by omega) (Over.mk (W'.hom ≫ W.hom)) v y) hsec
    exact (hH.isInternalHom.symm_naturality j q.left (balancedHomDg β hij V x)).symm.trans
      (congrArg (hH.isInternalHom.sectionsEquiv j W.left).symm hres)
  isLinear i j hij p V x b := by
    change (hH.isInternalHom.sectionsEquiv (j + p) V.left).symm
        (balancedHomDg β (by omega) V ((M.mul i p).app (Opposite.op V.left) x b)) =
      (H.mul j p).app (Opposite.op V.left)
        ((hH.isInternalHom.sectionsEquiv j V.left).symm (balancedHomDg β hij V x)) b
    rw [Equiv.symm_apply_eq]
    refine LocalHom.ext fun j' k hj'k W y => ?_
    have hl : (balancedHomDg β (show i + p + n = j + p by omega) V
            ((M.mul i p).app (Opposite.op V.left) x b)).app j' k hj'k W y =
        β.app (i + p) j' k (by omega) (Over.mk (W.hom ≫ V.hom))
          ((M.complex.X (i + p)).val.map W.hom.op
            ((M.mul i p).app (Opposite.op V.left) x b)) y := rfl
    have hr : (hH.isInternalHom.sectionsEquiv (j + p) V.left
            ((H.mul j p).app (Opposite.op V.left)
              ((hH.isInternalHom.sectionsEquiv j V.left).symm
                (balancedHomDg β hij V x)) b)).app j' k hj'k W y =
        β.app i (p + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
          ((M.complex.X i).val.map W.hom.op x)
          ((N.leftMul p j').app (Opposite.op W.left)
            ((A.complex.X p).val.map W.hom.op b) y) := by
      rw [hH.mul_spec j p V.left _ b j' k hj'k W y, Equiv.apply_symm_apply]
      rfl
    refine hl.trans (Eq.trans ?_ hr.symm)
    rw [(M.mul i p).naturality W.hom.op x b]
    exact β.balanced i p j' k (by omega) (Over.mk (W.hom ≫ V.hom)) _ _ y

/-- The value of `ofBalancedDg hH β` at a local section `x` of `M^i` is the section of the
internal hom naming the local homomorphism `balancedHomDg β hij V x`. -/
theorem ofBalancedDg_app (hH : IsSheafHom N L H) {U : C}
    (β : LocalBalancedBilinear M N L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (ofBalancedDg hH β).app i j hij V x =
      (hH.isInternalHom.sectionsEquiv j V.left).symm (balancedHomDg β hij V x) := rfl

/-! ### The two constructions are inverse to one another -/

/-- `ofBalancedDg hH` is a left inverse of `toBalancedDg hH`. -/
theorem ofBalancedDg_toBalancedDg (hH : IsSheafHom N L H) {U : C}
    (f : LocalHom M H n U) : ofBalancedDg hH (toBalancedDg hH f) = f := by
  refine LocalHom.ext fun i j hij V x => ?_
  rw [ofBalancedDg_app, Equiv.symm_apply_eq]
  refine LocalHom.ext fun j' k hj'k W y => ?_
  rw [balancedHomDg_eq]
  refine (balancedValDg_congr hH f i j' k (i + n) j rfl hij (by omega) (by omega)
    (Over.mk (W.hom ≫ V.hom)) _ y).trans ?_
  have key : balancedValDg hH f i j' k j hij hj'k (Over.mk (W.hom ≫ V.hom))
        ((M.complex.X i).val.map W.hom.op x) y =
      (hH.isInternalHom.sectionsEquiv j W.left (f.app i j hij (Over.mk (W.hom ≫ V.hom))
        ((M.complex.X i).val.map W.hom.op x))).app j' k hj'k (Over.mk (𝟙 W.left)) y := rfl
  have hnat : f.app i j hij (Over.mk (W.hom ≫ V.hom))
        ((M.complex.X i).val.map W.hom.op x) =
      (H.complex.X j).val.map W.hom.op (f.app i j hij V x) :=
    (f.naturality i j hij (Over.homMk W.hom rfl : Over.mk (W.hom ≫ V.hom) ⟶ V) x).symm
  rw [key, hnat]
  exact hH.isInternalHom.sectionsEquiv_map_top j W.hom (f.app i j hij V x) j' k hj'k y

/-- `toBalancedDg hH` is a left inverse of `ofBalancedDg hH`. -/
theorem toBalancedDg_ofBalancedDg (hH : IsSheafHom N L H) {U : C}
    (β : LocalBalancedBilinear M N L n U) : toBalancedDg hH (ofBalancedDg hH β) = β := by
  refine LocalBalancedBilinear.ext fun i j k hijk V x y => ?_
  have key : (toBalancedDg hH (ofBalancedDg hH β)).app i j k hijk V x y =
      (hH.isInternalHom.sectionsEquiv (i + n) V.left
        ((hH.isInternalHom.sectionsEquiv (i + n) V.left).symm
          (balancedHomDg β rfl V x))).app j k (by omega) (Over.mk (𝟙 V.left)) y := rfl
  rw [key, Equiv.apply_symm_apply, balancedHomDg_eq]
  exact β.app_top i j k hijk V x y

/-- The degree-`n` local homomorphisms `M|_U → SheafHom^dg_B(N, L)|_U` of right differential
graded `A`-modules are the `A`-balanced bilinear families of degree `n` over `U`. This is the
local form of the tensor-hom adjunction. -/
noncomputable def balancedEquivDg (hH : IsSheafHom N L H)
    (M : DifferentialGradedModule.{t, a, w} A) (n : ℤ) (U : C) :
    LocalHom M H n U ≃ LocalBalancedBilinear M N L n U where
  toFun := toBalancedDg hH
  invFun := ofBalancedDg hH
  left_inv := ofBalancedDg_toBalancedDg hH
  right_inv := toBalancedDg_ofBalancedDg hH

/-- `toBalancedDg hH` commutes with restriction along a morphism `q : U' ⟶ U` of the site. -/
theorem toBalancedDg_restrict (hH : IsSheafHom N L H) {U U' : C}
    (q : U' ⟶ U) (f : LocalHom M H n U) :
    (toBalancedDg hH f).restrict q = toBalancedDg hH (f.restrict q) := by
  refine LocalBalancedBilinear.ext fun i j k hijk V x y => ?_
  rfl

/-- `ofBalancedDg hH` commutes with restriction along a morphism `q : U' ⟶ U` of the site. -/
theorem ofBalancedDg_restrict (hH : IsSheafHom N L H) {U U' : C}
    (q : U' ⟶ U) (β : LocalBalancedBilinear M N L n U) :
    (ofBalancedDg hH β).restrict q = ofBalancedDg hH (β.restrict q) := by
  have h := toBalancedDg_restrict hH q (ofBalancedDg hH β)
  rw [toBalancedDg_ofBalancedDg] at h
  rw [h, ofBalancedDg_toBalancedDg]

/-- The value, on a local section of `N`, of the local homomorphism named by a section of the
internal hom which `ofBalancedDg` attaches to a local section of `M`. -/
theorem ofBalancedDg_sectionsEquiv_app (hH : IsSheafHom N L H) {U : C}
    (β : LocalBalancedBilinear M N L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) (j' k : ℤ) (hj'k : j' + j = k)
    (W : Over V.left) (y : (N.complex.X j').val.obj (Opposite.op W.left)) :
    (hH.isInternalHom.sectionsEquiv j V.left
        ((ofBalancedDg hH β).app i j hij V x)).app j' k hj'k W y =
      β.app i j' k (by omega) (Over.mk (W.hom ≫ V.hom))
        ((M.complex.X i).val.map W.hom.op x) y := by
  rw [ofBalancedDg_app, Equiv.apply_symm_apply, balancedHomDg_eq]

end LocalAdjunction

/-! ### The second displayed identity -/

section SecondIdentity

variable {M H : DifferentialGradedModule.{t, a, w} A}
  {N : DifferentialGradedBimodule.{t, a, z} A B} {L T : DifferentialGradedModule.{t, a, s} B}
  {G : CochainComplex (SheafOfModules.{g} R) ℤ}

/-- The identification of the degree-`n` sections of `SheafHom^dg_B(M ⊗_A N, L)` over `U` with
the degree-`n` local homomorphisms `M|_U → SheafHom^dg_B(N, L)|_U`: a section is read as a local
homomorphism out of the tensor product, hence as a balanced bilinear family, hence as a local
homomorphism into the internal hom. -/
noncomputable def tensorSectionsEquiv (hT : IsTensorProduct M N T)
    (hH : IsSheafHom N L H) (hG : IsInternalHom T L G) (n : ℤ) (U : C) :
    (G.X n).val.obj (Opposite.op U) ≃ LocalHom M H n U :=
  (hG.sectionsEquiv n U).trans ((hT.universal L n U).trans (balancedEquivDg hH M n U).symm)

/-- The identification above sends a section of `SheafHom^dg_B(M ⊗_A N, L)` to the local
homomorphism `x ↦ (y ↦ φ (x ⊗ y))`, where `φ` is the local homomorphism out of the tensor
product that the section names. -/
theorem tensorSectionsEquiv_eval (hT : IsTensorProduct M N T)
    (hH : IsSheafHom N L H) (hG : IsInternalHom T L G) (n : ℤ) (U : C)
    (p : (G.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) (j' k : ℤ) (hj'k : j' + j = k)
    (W : Over V.left) (y : (N.complex.X j').val.obj (Opposite.op W.left)) :
    (hH.isInternalHom.sectionsEquiv j V.left
        ((tensorSectionsEquiv hT hH hG n U p).app i j hij V x)).app j' k hj'k W y =
      (hG.sectionsEquiv n U p).app (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
        (hT.tmul i j' (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
          ((M.complex.X i).val.map W.hom.op x) y) :=
  (ofBalancedDg_sectionsEquiv_app hH (hT.universal L n U (hG.sectionsEquiv n U p)) i j hij V x
      j' k hj'k W y).trans
    (hT.universal_app L n U (hG.sectionsEquiv n U p) i j' k (by omega)
      (Over.mk (W.hom ≫ V.hom)) ((M.complex.X i).val.map W.hom.op x) y)

/-- The identification above is compatible with the differentials: this is the differential
graded content of the second displayed identity. -/
theorem tensorSectionsEquiv_d (hT : IsTensorProduct M N T)
    (hH : IsSheafHom N L H) (hG : IsInternalHom T L G) (n m : ℤ) (U : C)
    (p : (G.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + m = j) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (tensorSectionsEquiv hT hH hG m U ((G.d n m).val.app (Opposite.op U) p)).app i j hij V x =
      localDiffApp (tensorSectionsEquiv hT hH hG n U p).toLocalGradedHom m i j hij V x := by
  refine hH.isInternalHom.sections_ext fun j' k hj'k W y => ?_
  have hlhs := (tensorSectionsEquiv_eval hT hH hG m U
      ((G.d n m).val.app (Opposite.op U) p) i j hij V x j' k hj'k W y).trans
    (hG.sectionsEquiv_d n m U p (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
      (hT.tmul i j' (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
        ((M.complex.X i).val.map W.hom.op x) y))
  rw [hlhs]
  by_cases hm : m = n + 1
  · subst hm
    have hdnat : (M.complex.X (i + 1)).val.map W.hom.op
          ((M.complex.d i (i + 1)).val.app (Opposite.op V.left) x) =
        (M.complex.d i (i + 1)).val.app (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
          ((M.complex.X i).val.map W.hom.op x) :=
      homSections_naturality (M.complex.d i (i + 1)) W.hom.op x
    rw [localDiffApp_eq (hG.sectionsEquiv n U p).toLocalGradedHom (n + 1) (i + j') k
        (i + j' + n) (i + j' + 1) (by omega) (by omega) (by omega) (Over.mk (W.hom ≫ V.hom)) _,
      hT.tmul_d_castHom i j' (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
        ((M.complex.X i).val.map W.hom.op x) y,
      map_add, map_zsmul,
      LocalGradedHom.app_castHom_src (hG.sectionsEquiv n U p).toLocalGradedHom
        (add_right_comm i 1 j') (by omega) (Over.mk (W.hom ≫ V.hom)) _,
      LocalGradedHom.app_castHom_src (hG.sectionsEquiv n U p).toLocalGradedHom
        (add_assoc i j' 1).symm (by omega) (Over.mk (W.hom ≫ V.hom)) _,
      localDiffApp_eq (tensorSectionsEquiv hT hH hG n U p).toLocalGradedHom (n + 1) i j
        (i + n) (i + 1) hij rfl (by omega) V x,
      hH.isInternalHom.sectionsEquiv_add j V.left _ _ j' k hj'k W y,
      hH.isInternalHom.sectionsEquiv_zsmul j V.left _ _ j' k hj'k W y,
      hH.isInternalHom.sectionsEquiv_d (i + n) j V.left
        ((tensorSectionsEquiv hT hH hG n U p).app i (i + n) rfl V x) j' k hj'k W y,
      localDiffApp_eq (hH.isInternalHom.sectionsEquiv (i + n) V.left
          ((tensorSectionsEquiv hT hH hG n U p).app i (i + n) rfl V x)).toLocalGradedHom
        j j' k (i + j' + n) (j' + 1) hj'k (by omega) (by omega) W y,
      tensorSectionsEquiv_eval hT hH hG n U p i (i + n) rfl V x j' (i + j' + n) (by omega) W y,
      tensorSectionsEquiv_eval hT hH hG n U p i (i + n) rfl V x (j' + 1) k (by omega) W
        ((N.toRightModule.complex.d j' (j' + 1)).val.app (Opposite.op W.left) y),
      tensorSectionsEquiv_eval hT hH hG n U p (i + 1) j (by omega) V
        ((M.complex.d i (i + 1)).val.app (Opposite.op V.left) x) j' k (by omega) W y,
      hdnat]
    obtain rfl : j = i + n + 1 := by omega
    simp only [DifferentialGradedBimodule.toRightModule_complex, Over.mk_left]
    rw [smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add,
      show n + 1 + i = i + n + 1 from by omega]
    abel
  · rw [localDiffApp_of_ne (hG.sectionsEquiv n U p).toLocalGradedHom m (i + j') k (by omega) hm
        (Over.mk (W.hom ≫ V.hom)) _,
      localDiffApp_of_ne (tensorSectionsEquiv hT hH hG n U p).toLocalGradedHom m i j hij hm V x,
      hH.isInternalHom.sectionsEquiv_zero]

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, second identity: a
complex of sheaves of `R`-modules which is the internal hom `SheafHom^dg_B(M ⊗_A N, L)` is also
the internal hom `SheafHom^dg_A(M, SheafHom^dg_B(N, L))`, differentials included. -/
@[stacks 0FRS "SheafHom^dg_B(M ⊗_A N, L) = SheafHom^dg_A(M, SheafHom^dg_B(N, L))"]
noncomputable def isInternalHom_tensor (hT : IsTensorProduct M N T)
    (hH : IsSheafHom N L H) (hG : IsInternalHom T L G) :
    IsInternalHom M H G where
  sectionsEquiv n U := tensorSectionsEquiv hT hH hG n U
  sectionsEquiv_add n U p q i j hij V x := by
    refine hH.isInternalHom.sections_ext fun j' k hj'k W y => ?_
    rw [tensorSectionsEquiv_eval hT hH hG n U (p + q) i j hij V x j' k hj'k W y,
      hH.isInternalHom.sectionsEquiv_add j V.left _ _ j' k hj'k W y,
      tensorSectionsEquiv_eval hT hH hG n U p i j hij V x j' k hj'k W y,
      tensorSectionsEquiv_eval hT hH hG n U q i j hij V x j' k hj'k W y]
    exact hG.sectionsEquiv_add n U p q (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom)) _
  sectionsEquiv_smul n U r p i j hij V x := by
    refine hH.isInternalHom.sections_ext fun j' k hj'k W y => ?_
    have hr : R.obj.map (Over.mk (W.hom ≫ V.hom)).hom.op r =
        R.obj.map W.hom.op (R.obj.map V.hom.op r) := by
      rw [show (Over.mk (W.hom ≫ V.hom)).hom.op = V.hom.op ≫ W.hom.op from rfl, R.obj.map_comp]
      rfl
    rw [tensorSectionsEquiv_eval hT hH hG n U (r • p) i j hij V x j' k hj'k W y,
      hH.isInternalHom.sectionsEquiv_smul j V.left _ _ j' k hj'k W y,
      tensorSectionsEquiv_eval hT hH hG n U p i j hij V x j' k hj'k W y,
      hG.sectionsEquiv_smul n U r p (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom)), hr]
  sectionsEquiv_naturality n {U U'} q p i j hij V := by
    have hres : hG.sectionsEquiv n U' ((G.X n).val.map q.op p) =
        (hG.sectionsEquiv n U p).restrict q :=
      LocalHom.ext fun i' j' hij' V' x =>
        DFunLike.congr_fun (hG.sectionsEquiv_naturality n q p i' j' hij' V') x
    have huniv : hT.universal L n U' (hG.sectionsEquiv n U' ((G.X n).val.map q.op p)) =
        (hT.universal L n U (hG.sectionsEquiv n U p)).restrict q := by
      rw [hres]
      refine LocalBalancedBilinear.ext fun i' j' k hijk V' x y => ?_
      rw [LocalBalancedBilinear.restrict_app,
        ← hT.universal_restrict L n q (hG.sectionsEquiv n U p) i' j' k hijk V' x y]
    have key : ofBalancedDg hH (hT.universal L n U'
          (hG.sectionsEquiv n U' ((G.X n).val.map q.op p))) =
        (ofBalancedDg hH (hT.universal L n U (hG.sectionsEquiv n U p))).restrict q := by
      rw [ofBalancedDg_restrict, huniv]
    exact congrArg (fun z : LocalHom M H n U' => z.app i j hij V) key
  sectionsEquiv_d n m U p i j hij V x := tensorSectionsEquiv_d hT hH hG n m U p i j hij V x

/-! ### Functoriality of the second displayed identity -/

section Naturality

variable {M' H' : DifferentialGradedModule.{t, a, w} A}
  {N' : DifferentialGradedBimodule.{t, a, z} A B}
  {L' T' : DifferentialGradedModule.{t, a, s} B}
  {G' : CochainComplex (SheafOfModules.{g} R) ℤ}

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, second identity,
functoriality in `M`: a morphism `u : M' ⟶ M` of right differential graded `A`-modules induces
`t : M' ⊗_A N ⟶ M ⊗_A N` and hence `α : SheafHom^dg_B(M ⊗_A N, L) ⟶ SheafHom^dg_B(M' ⊗_A N, L)`,
and `α` is also the map that the second identity attaches to `u`, namely precomposition with
`u` on `SheafHom^dg_A(M, SheafHom^dg_B(N, L))`. -/
@[stacks 0FRS "functoriality of the internal-hom identity in M, on local sections"]
theorem tensorSectionsEquiv_naturality_left (hT : IsTensorProduct M N T)
    (hT' : IsTensorProduct M' N T') (hH : IsSheafHom N L H) (hG : IsInternalHom T L G)
    (hG' : IsInternalHom T' L G') (u : M' ⟶ M) (t : T' ⟶ T) (α : G ⟶ G')
    (ht : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (M'.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U),
      (t.toHomologicalComplex.f (i + j)).val.app U (hT'.tmul i j U x y) =
        hT.tmul i j U ((u.toHomologicalComplex.f i).val.app U x) y)
    (hα : ∀ (n : ℤ) (U : C) (p : (G.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
      (V : Over U) (x : (T'.complex.X i).val.obj (Opposite.op V.left)),
      (hG'.sectionsEquiv n U ((α.f n).val.app (Opposite.op U) p)).app i j hij V x =
        (hG.sectionsEquiv n U p).app i j hij V
          ((t.toHomologicalComplex.f i).val.app (Opposite.op V.left) x))
    (n : ℤ) (U : C) (p : (G.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (M'.complex.X i).val.obj (Opposite.op V.left)) :
    (tensorSectionsEquiv hT' hH hG' n U ((α.f n).val.app (Opposite.op U) p)).app i j hij V x =
      (tensorSectionsEquiv hT hH hG n U p).app i j hij V
        ((u.toHomologicalComplex.f i).val.app (Opposite.op V.left) x) := by
  refine hH.isInternalHom.sections_ext fun j' k hj'k W y => ?_
  have hnat : (M.complex.X i).val.map W.hom.op
        ((u.toHomologicalComplex.f i).val.app (Opposite.op V.left) x) =
      (u.toHomologicalComplex.f i).val.app (Opposite.op W.left)
        ((M'.complex.X i).val.map W.hom.op x) :=
    homSections_naturality (u.toHomologicalComplex.f i) W.hom.op x
  rw [tensorSectionsEquiv_eval hT' hH hG' n U _ i j hij V x j' k hj'k W y,
    hα n U p (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom)) _,
    ht i j' (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
      ((M'.complex.X i).val.map W.hom.op x) y,
    tensorSectionsEquiv_eval hT hH hG n U p i j hij V _ j' k hj'k W y, hnat]
  rfl

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, second identity,
functoriality in `L`: a morphism `k : L ⟶ L'` of right differential graded `B`-modules induces
`α : SheafHom^dg_B(M ⊗_A N, L) ⟶ SheafHom^dg_B(M ⊗_A N, L')` and
`g : SheafHom^dg_B(N, L) ⟶ SheafHom^dg_B(N, L')`, and under the second identity `α` is
postcomposition with `g`. -/
@[stacks 0FRS "functoriality of the internal-hom identity in L, on local sections"]
theorem tensorSectionsEquiv_naturality_right (hT : IsTensorProduct M N T)
    (hH : IsSheafHom N L H) (hH' : IsSheafHom N L' H') (hG : IsInternalHom T L G)
    (hG' : IsInternalHom T L' G') (k : L ⟶ L') (g : H ⟶ H') (α : G ⟶ G')
    (hg : ∀ (m : ℤ) (U : C) (q : (H.complex.X m).val.obj (Opposite.op U)) (i j : ℤ)
      (hij : i + m = j) (V : Over U)
      (y : (N.complex.X i).val.obj (Opposite.op V.left)),
      (hH'.isInternalHom.sectionsEquiv m U
          ((g.toHomologicalComplex.f m).val.app (Opposite.op U) q)).app i j hij V y =
        (k.toHomologicalComplex.f j).val.app (Opposite.op V.left)
          ((hH.isInternalHom.sectionsEquiv m U q).app i j hij V y))
    (hα : ∀ (n : ℤ) (U : C) (p : (G.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
      (V : Over U) (x : (T.complex.X i).val.obj (Opposite.op V.left)),
      (hG'.sectionsEquiv n U ((α.f n).val.app (Opposite.op U) p)).app i j hij V x =
        (k.toHomologicalComplex.f j).val.app (Opposite.op V.left)
          ((hG.sectionsEquiv n U p).app i j hij V x))
    (n : ℤ) (U : C) (p : (G.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (tensorSectionsEquiv hT hH' hG' n U ((α.f n).val.app (Opposite.op U) p)).app i j hij V x =
      (g.toHomologicalComplex.f j).val.app (Opposite.op V.left)
        ((tensorSectionsEquiv hT hH hG n U p).app i j hij V x) := by
  refine hH'.isInternalHom.sections_ext fun j' k' hj'k W y => ?_
  rw [tensorSectionsEquiv_eval hT hH' hG' n U _ i j hij V x j' k' hj'k W y,
    hα n U p (i + j') k' (by omega) (Over.mk (W.hom ≫ V.hom)) _,
    hg j V.left _ j' k' hj'k W y,
    tensorSectionsEquiv_eval hT hH hG n U p i j hij V x j' k' hj'k W y]
  rfl

/-- **Tensor-hom adjunction for sheaves of differential graded modules**, second identity,
functoriality in `N`: a morphism `σ : N ⟶ N'` of differential graded `(A, B)`-bimodules induces
`t : M ⊗_A N ⟶ M ⊗_A N'`, hence `α : SheafHom^dg_B(M ⊗_A N', L) ⟶ SheafHom^dg_B(M ⊗_A N, L)`,
and `g : SheafHom^dg_B(N', L) ⟶ SheafHom^dg_B(N, L)`; under the second identity `α` is
postcomposition with `g`. -/
@[stacks 0FRS "functoriality of the internal-hom identity in N, on local sections"]
theorem tensorSectionsEquiv_naturality_bimodule (hT : IsTensorProduct M N T)
    (hT' : IsTensorProduct M N' T') (hH : IsSheafHom N L H) (hH' : IsSheafHom N' L H')
    (hG : IsInternalHom T L G) (hG' : IsInternalHom T' L G')
    (σ : N ⟶ N') (t : T ⟶ T') (g : H' ⟶ H) (α : G' ⟶ G)
    (ht : ∀ (i j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U),
      (t.toHomologicalComplex.f (i + j)).val.app U (hT.tmul i j U x y) =
        hT'.tmul i j U x ((σ.toHomologicalComplex.f j).val.app U y))
    (hg : ∀ (m : ℤ) (U : C) (q : (H'.complex.X m).val.obj (Opposite.op U)) (i j : ℤ)
      (hij : i + m = j) (V : Over U)
      (y : (N.complex.X i).val.obj (Opposite.op V.left)),
      (hH.isInternalHom.sectionsEquiv m U
          ((g.toHomologicalComplex.f m).val.app (Opposite.op U) q)).app i j hij V y =
        (hH'.isInternalHom.sectionsEquiv m U q).app i j hij V
          ((σ.toHomologicalComplex.f i).val.app (Opposite.op V.left) y))
    (hα : ∀ (n : ℤ) (U : C) (p : (G'.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
      (V : Over U) (x : (T.complex.X i).val.obj (Opposite.op V.left)),
      (hG.sectionsEquiv n U ((α.f n).val.app (Opposite.op U) p)).app i j hij V x =
        (hG'.sectionsEquiv n U p).app i j hij V
          ((t.toHomologicalComplex.f i).val.app (Opposite.op V.left) x))
    (n : ℤ) (U : C) (p : (G'.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (tensorSectionsEquiv hT hH hG n U ((α.f n).val.app (Opposite.op U) p)).app i j hij V x =
      (g.toHomologicalComplex.f j).val.app (Opposite.op V.left)
        ((tensorSectionsEquiv hT' hH' hG' n U p).app i j hij V x) := by
  refine hH.isInternalHom.sections_ext fun j' k hj'k W y => ?_
  rw [tensorSectionsEquiv_eval hT hH hG n U _ i j hij V x j' k hj'k W y,
    hα n U p (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom)) _,
    ht i j' (Opposite.op (Over.mk (W.hom ≫ V.hom)).left)
      ((M.complex.X i).val.map W.hom.op x) y,
    hg j V.left _ j' k hj'k W y,
    tensorSectionsEquiv_eval hT' hH' hG' n U p i j hij V x j' k hj'k W _]
  rfl

end Naturality

end SecondIdentity

end SheafOfModules

end
