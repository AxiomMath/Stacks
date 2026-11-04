module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInternalHom

/-!
# Tensor products of sheaves of differential graded modules

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` and `B` be sheaves of differential
graded `R`-algebras, let `M` be a right differential graded `A`-module and let `N` be a
differential graded `(A, B)`-bimodule. The tensor product `M ⊗_A N` is the right differential
graded `B`-module whose degree-`k` part is built from `⨁_{i + j = k} M^i ⊗_R N^j` by imposing
the relations `x a ⊗ y = x ⊗ a y`, with right `B`-action `(x ⊗ y) b = x ⊗ y b` and differential

`d (x ⊗ y) = d x ⊗ y + (-1)^i x ⊗ d y`

on a homogeneous local section `x` of degree `i`.

This file pins that module down by its universal property: an `A`-balanced bilinear family of
degree `n` out of `M` and `N` is the same thing as a degree-`n` homomorphism of right
differential graded `B`-modules out of `M ⊗_A N`. The existence of such a module is not
asserted here.

## Main definitions

* `SheafOfModules.LocalBalancedBilinear` is an `A`-balanced bilinear family of degree `n` over
  an object `U` of the site: maps `M^i|_U × N^j|_U → L^{i + j + n}|_U` which are bilinear over
  the sheaf of rings, compatible with restriction, `A`-balanced (`x a ⊗ y` and `x ⊗ a y` have
  the same image) and `B`-linear in the second variable.
* `SheafOfModules.IsTensorProduct` says that a right differential graded `B`-module `T` is the
  tensor product `M ⊗_A N`: it carries a universal `A`-balanced bilinear map `tmul`, the right
  `B`-action on `T` is `(x ⊗ y) b = x ⊗ y b`, the differential of `T` obeys the signed Leibniz
  rule, and composing a degree-`n` local homomorphism out of `T` with `tmul` is a bijection
  onto the `A`-balanced bilinear families of degree `n`.
* `SheafOfModules.IsTensorProduct.uniqueIso` is the canonical isomorphism between two tensor
  products of the same pair; `SheafOfModules.IsTensorProduct.descend` is the degree-zero local
  homomorphism underlying it and `SheafOfModules.IsTensorProduct.descendDgHom` the resulting
  homomorphism of right differential graded `B`-modules.
* `SheafOfModules.TensorFunctorData` packages the tensor products with a fixed bimodule `N` as
  a functor `- ⊗_A N : Mod^dg(A, d) ⥤ Mod^dg(B, d)`, together with the description of its
  action on morphisms, and `SheafOfModules.TensorFunctorData.uniqueIso` compares two such
  functors objectwise.
* `SheafOfModules.LocalHom.restrict` restricts a local homomorphism along a morphism of the
  site, `SheafOfModules.LocalHom.zero` is the zero local homomorphism, and
  `SheafOfModules.castHom₂` transports the target degree of a biadditive map on local sections
  along an equality of degrees.

## Main results

* `SheafOfModules.IsTensorProduct.localHom_ext`: two degree-`n` local homomorphisms out of a
  tensor product which agree on the image of `tmul` are equal.
* `SheafOfModules.IsTensorProduct.tmul_add_left`, `tmul_add_right`, `tmul_zero_left` and
  `tmul_zero_right`: `tmul` is additive in each variable and kills zero in each variable.
* `SheafOfModules.IsTensorProduct.uniqueIso`: two right differential graded `B`-modules which
  are both the tensor product `M ⊗_A N` are isomorphic, by the isomorphism determined by
  `x ⊗ y ↦ x ⊗ y`. Its two halves are
  `SheafOfModules.IsTensorProduct.descendDiff_eq_zero`, that the comparison commutes with the
  differentials, and `SheafOfModules.IsTensorProduct.descendHom_comp`, that the two
  comparisons are mutually inverse.

## Implementation notes

The tensor product cannot be written down by a formula here: the monoidal structure on
presheaves of modules is defined only over a presheaf of *commutative* rings, and sheaves of
modules carry limits, colimits, abelianness and change of rings but nothing monoidal. So, as
for the internal hom, the object is pinned by a universal property instead. The datum `tmul`
is given on local sections over the objects of the site, and the universal property is stated
over each object `U` separately, in terms of the degree-`n` local homomorphisms of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInternalHom.lean`; this pins
the restriction of `T` to each slice site, which is what makes the characterisation local and
determines `T` up to canonical isomorphism (`IsTensorProduct.uniqueIso`).

Degrees are carried in two different ways, each chosen so that no formula needs a
heterogeneous equality. The target degree of `tmul` is `i + j` on the nose, as for the two
actions of `DifferentialGradedBimodule`, so the associativity-style clauses `tmul_balanced`
and `tmul_rightMul` are stated with `HEq` and the Leibniz rule `tmul_d` with
`SheafOfModules.gradedCast`, exactly as for the actions of a bimodule. The target degree of a
balanced bilinear *family* is instead an independent degree `k` together with a proof of
`i + j + n = k`, as for the cochains of `CochainComplex.HomComplex`, which is what lets the
universal property and its consequences be stated without transports.

The test module `L` of the universal property lies in the same module universe as `T`,
because a structure field cannot quantify over a universe. This is the same restriction as for
`SheafOfModules.InternalHomFunctorData`, and it is what the functor `- ⊗_A N` needs anyway.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebras, the module `M` and the
bimodule `N` are independent; a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory

universe t a w z s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R}

/-- Transport the target degree of a biadditive map on local sections along an equality of
degrees. -/
def castHom₂ (Y : SheafOfModules.{w} R) (Z : SheafOfModules.{z} R)
    (X : ℤ → SheafOfModules.{s} R) {k k' : ℤ} (h : k = k') (U : Cᵒᵖ)
    (f : Y.val.obj U →+ Z.val.obj U →+ (X k).val.obj U) :
    Y.val.obj U →+ Z.val.obj U →+ (X k').val.obj U := by
  subst h; exact f

/-- Transporting the target degree of a biadditive map transports its values. -/
theorem castHom₂_apply (Y : SheafOfModules.{w} R) (Z : SheafOfModules.{z} R)
    (X : ℤ → SheafOfModules.{s} R) {k k' : ℤ} (h : k = k') (U : Cᵒᵖ)
    (f : Y.val.obj U →+ Z.val.obj U →+ (X k).val.obj U) (y : Y.val.obj U) (zz : Z.val.obj U) :
    castHom₂ Y Z X h U f y zz = castHom X h U (f y zz) := by
  subst h; rfl

/-- Transporting a local section along a reflexive equality of degrees does nothing. -/
theorem castHom_self (X : ℤ → SheafOfModules.{s} R) {i : ℤ} (h : i = i) (U : Cᵒᵖ)
    (x : (X i).val.obj U) : castHom X h U x = x := rfl

/-- Transporting a local section twice is transporting it once. -/
theorem castHom_castHom (X : ℤ → SheafOfModules.{s} R) {i j k : ℤ} (h : i = j) (h' : j = k)
    (U : Cᵒᵖ) (x : (X i).val.obj U) :
    castHom X h' U (castHom X h U x) = castHom X (h.trans h') U x := by
  subst h; subst h'; rfl

/-- Two local sections which are heterogeneously equal become equal after transport to a
common degree. -/
theorem castHom_heq (X : ℤ → SheafOfModules.{s} R) {i j k : ℤ} (hi : i = k) (hj : j = k)
    (U : Cᵒᵖ) {x : (X i).val.obj U} {y : (X j).val.obj U} (h : HEq x y) :
    castHom X hi U x = castHom X hj U y := by
  subst hi; subst hj; exact eq_of_heq h

/-- The differential of a cochain complex of sheaves of modules into a degree reached by
transport is the transport of the differential. -/
theorem d_app_castHom (X : CochainComplex (SheafOfModules.{s} R) ℤ) {i j j' : ℤ} (h : j = j')
    (U : Cᵒᵖ) (x : (X.X i).val.obj U) :
    (X.d i j').val.app U x = castHom X.X h U ((X.d i j).val.app U x) := by
  subst h; rfl

/-- The right action of a differential graded module on a transported local section is the
transport of the action. -/
theorem mul_app_castHom (T : DifferentialGradedModule.{t, a, s} B) {k k' : ℤ} (h : k = k')
    (p : ℤ) (U : Cᵒᵖ) (x : (T.complex.X k).val.obj U) (b : (B.complex.X p).val.obj U) :
    (T.mul k' p).app U (castHom T.complex.X h U x) b =
      castHom T.complex.X (by omega : k + p = k' + p) U ((T.mul k p).app U x b) := by
  subst h; rfl

/-- The restriction maps of a sheaf of modules are compatible with subtraction of local
sections. -/
theorem map_sub_sections (X : SheafOfModules.{s} R) {U V : Cᵒᵖ} (g : U ⟶ V)
    (x y : X.val.obj U) : X.val.map g (x - y) = X.val.map g x - X.val.map g y :=
  (X.val.map g).hom.toAddMonoidHom.map_sub x y

/-- Transporting a sum of local sections along an equality of degrees is the sum of the
transports. -/
theorem castHom_add (X : ℤ → SheafOfModules.{s} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x y : (X i).val.obj U) :
    castHom X h U (x + y) = castHom X h U x + castHom X h U y :=
  map_add _ _ _

/-- Transporting an integer multiple of a local section along an equality of degrees is the
multiple of the transport. -/
theorem castHom_zsmul (X : ℤ → SheafOfModules.{s} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (k : ℤ) (x : (X i).val.obj U) :
    castHom X h U (k • x) = k • castHom X h U x :=
  map_zsmul _ _ _

/-- Restrict a degree-`n` map of the underlying graded modules along a morphism `U' ⟶ U` of the
site, by viewing the objects of the slice site over `U'` as objects over `U`. -/
def LocalGradedHom.restrict {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L : DifferentialGradedModule.{t, a, z} A'}
    {n : ℤ} {U U' : C} (g : U' ⟶ U) (f : LocalGradedHom K L n U) :
    LocalGradedHom K L n U' where
  app i j hij V := f.app i j hij (Over.mk (V.hom ≫ g))
  map_smul i j hij V r x := f.map_smul i j hij (Over.mk (V.hom ≫ g)) r x
  naturality i j hij {V W} q x :=
    f.naturality i j hij (V := Over.mk (V.hom ≫ g)) (W := Over.mk (W.hom ≫ g))
      (Over.homMk q.left (show q.left ≫ V.hom ≫ g = W.hom ≫ g by
        rw [← Category.assoc, Over.w q])) x

/-- Restrict a degree-`n` local homomorphism of right differential graded modules along a
morphism `U' ⟶ U` of the site. -/
def LocalHom.restrict {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L : DifferentialGradedModule.{t, a, z} A'}
    {n : ℤ} {U U' : C} (g : U' ⟶ U) (f : LocalHom K L n U) : LocalHom K L n U' where
  toLocalGradedHom := f.toLocalGradedHom.restrict g
  isLinear i j hij p V x b := f.isLinear i j hij p (Over.mk (V.hom ≫ g)) x b

/-- The zero degree-`n` local homomorphism of right differential graded modules over `U`. -/
def LocalHom.zero {A' : DifferentialGradedAlgebra.{t, a} R}
    (K : DifferentialGradedModule.{t, a, w} A') (L : DifferentialGradedModule.{t, a, z} A')
    (n : ℤ) (U : C) : LocalHom K L n U where
  app _ _ _ _ := 0
  map_smul _ _ _ _ r _ := (smul_zero r).symm
  naturality i j hij {V W} q x := by
    refine Eq.trans ?_ (AddMonoidHom.zero_apply _).symm
    rw [AddMonoidHom.zero_apply, map_zero]
  isLinear i j hij p V x b := by
    simp only [AddMonoidHom.zero_apply, map_zero]

/-- Two equal local homomorphisms have the same values on local sections. -/
theorem LocalHom.app_congr {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L : DifferentialGradedModule.{t, a, z} A'}
    {n : ℤ} {U : C} {f f' : LocalHom K L n U} (h : f = f') (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    f.app i j hij V x = f'.app i j hij V x := by
  subst h; rfl

/-- The value of a local homomorphism over an object of the slice site depends only on the
structure morphism of that object. -/
theorem LocalGradedHom.app_mk_congr {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L : DifferentialGradedModule.{t, a, z} A'}
    {n : ℤ} {U U' : C} (f : LocalGradedHom K L n U) (i j : ℤ) (hij : i + n = j)
    {g g' : U' ⟶ U} (h : g = g')
    (x : (K.complex.X i).val.obj (Opposite.op U')) :
    f.app i j hij (Over.mk g) x = f.app i j hij (Over.mk g') x := by
  subst h; rfl

/-- A degree-zero map of the underlying graded modules commutes with transport along an
equality of degrees. -/
theorem LocalGradedHom.app_castHom {A' : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, w} A'} {L : DifferentialGradedModule.{t, a, z} A'}
    {U : C} (f : LocalGradedHom K L 0 U) {m m' : ℤ} (h : m = m') (V : Over U)
    (x : (K.complex.X m).val.obj (Opposite.op V.left)) :
    f.app m' m' (add_zero m') V (castHom K.complex.X h (Opposite.op V.left) x) =
      castHom L.complex.X h (Opposite.op V.left) (f.app m m (add_zero m) V x) := by
  subst h; rfl

/-- The zero local homomorphism has value zero on every local section. -/
@[simp]
theorem LocalHom.zero_app {A' : DifferentialGradedAlgebra.{t, a} R}
    (K : DifferentialGradedModule.{t, a, w} A') (L : DifferentialGradedModule.{t, a, z} A')
    (n : ℤ) (U : C) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    (LocalHom.zero K L n U).app i j hij V x = 0 := rfl

/-- The identity local homomorphism is the transport along the equality of its two degrees. -/
theorem LocalHom.id_app {A' : DifferentialGradedAlgebra.{t, a} R}
    (K : DifferentialGradedModule.{t, a, w} A') (U : C) (i j : ℤ) (hij : i + 0 = j)
    (V : Over U) (x : (K.complex.X i).val.obj (Opposite.op V.left)) :
    (LocalHom.id K U).app i j hij V x =
      castHom K.complex.X (by omega) (Opposite.op V.left) x := by
  obtain rfl : i = j := by omega
  rfl

/-- The signed Leibniz rule for the right action of a right differential graded module, with
the degree transports written as maps on local sections. -/
theorem DifferentialGradedModule.leibniz_castHom {A' : DifferentialGradedAlgebra.{t, a} R}
    (T : DifferentialGradedModule.{t, a, s} A') (n i : ℤ) (U : Cᵒᵖ)
    (x : (T.complex.X n).val.obj U) (y : (A'.complex.X i).val.obj U) :
    (T.complex.d (n + i) (n + i + 1)).val.app U ((T.mul n i).app U x y) =
      castHom T.complex.X (add_right_comm n 1 i) U
          ((T.mul (n + 1) i).app U ((T.complex.d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) • castHom T.complex.X (add_assoc n i 1).symm U
            ((T.mul n (i + 1)).app U x ((A'.complex.d i (i + 1)).val.app U y)) := by
  rw [T.leibniz n i U x y, castHom_apply, castHom_apply]

/-- An `A`-balanced bilinear family of degree `n` over `U`, from a right differential graded
`A`-module `M` and a differential graded `(A, B)`-bimodule `N` to a right differential graded
`B`-module `L`: maps `M^i|_U × N^j|_U → L^{i + j + n}|_U` which are bilinear over the sheaf of
rings, compatible with restriction, `A`-balanced and `B`-linear in the second variable. -/
@[stacks 0FRM "local balanced bilinear families, the universal property of the tensor product"]
structure LocalBalancedBilinear (M : DifferentialGradedModule.{t, a, w} A)
    (N : DifferentialGradedBimodule.{t, a, z} A B)
    (L : DifferentialGradedModule.{t, a, s} B) (n : ℤ) (U : C) where
  /-- The biadditive map on sections over an object `V ⟶ U` of the slice site, from degrees
  `i` and `j` to degree `k`, where `i + j + n = k`. -/
  app (i j k : ℤ) (hijk : i + j + n = k) (V : Over U) :
    (M.complex.X i).val.obj (Opposite.op V.left) →+
      (N.complex.X j).val.obj (Opposite.op V.left) →+
        (L.complex.X k).val.obj (Opposite.op V.left)
  /-- The maps are linear over the sheaf of rings in the first variable. -/
  map_smul_left (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (r : R.obj.obj (Opposite.op V.left))
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    app i j k hijk V (r • x) y = r • app i j k hijk V x y
  /-- The maps are linear over the sheaf of rings in the second variable. -/
  map_smul_right (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (r : R.obj.obj (Opposite.op V.left))
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    app i j k hijk V x (r • y) = r • app i j k hijk V x y
  /-- The maps commute with restriction inside the slice site. -/
  naturality (i j k : ℤ) (hijk : i + j + n = k) {V W : Over U} (g : W ⟶ V)
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (L.complex.X k).val.map g.left.op (app i j k hijk V x y) =
      app i j k hijk W ((M.complex.X i).val.map g.left.op x)
        ((N.complex.X j).val.map g.left.op y)
  /-- The maps are `A`-balanced: `x a ⊗ y` and `x ⊗ a y` have the same image. -/
  balanced (i p j k : ℤ) (hijk : i + p + j + n = k) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (a : (A.complex.X p).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    app (i + p) j k hijk V ((M.mul i p).app (Opposite.op V.left) x a) y =
      app i (p + j) k (by omega) V x ((N.leftMul p j).app (Opposite.op V.left) a y)
  /-- The maps are `B`-linear in the second variable. -/
  map_rightMul (i j p k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left))
      (b : (B.complex.X p).val.obj (Opposite.op V.left)) :
    app i (j + p) (k + p) (by omega) V x ((N.rightMul j p).app (Opposite.op V.left) y b) =
      (L.mul k p).app (Opposite.op V.left) (app i j k hijk V x y) b

/-- A balanced bilinear family is determined by its values on local sections. -/
@[ext]
theorem LocalBalancedBilinear.ext {M : DifferentialGradedModule.{t, a, w} A}
    {N : DifferentialGradedBimodule.{t, a, z} A B} {L : DifferentialGradedModule.{t, a, s} B}
    {n : ℤ} {U : C} {β γ : LocalBalancedBilinear M N L n U}
    (h : ∀ (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left)),
      β.app i j k hijk V x y = γ.app i j k hijk V x y) : β = γ := by
  obtain ⟨βapp, _, _, _, _, _⟩ := β
  obtain ⟨γapp, _, _, _, _, _⟩ := γ
  have happ : βapp = γapp := by
    funext i j k hijk V
    exact AddMonoidHom.ext fun x => AddMonoidHom.ext fun y => h i j k hijk V x y
  subst happ
  rfl

/-- A right differential graded `B`-module `T` is the tensor product `M ⊗_A N` of a right
differential graded `A`-module `M` with a differential graded `(A, B)`-bimodule `N` when it
carries an `A`-balanced bilinear map `tmul` of degree zero whose right `B`-action is
`(x ⊗ y) b = x ⊗ y b` and whose differential obeys `d (x ⊗ y) = d x ⊗ y + (-1)^i x ⊗ d y`, and
which is universal: composing a degree-`n` local homomorphism out of `T` with `tmul` is a
bijection onto the `A`-balanced bilinear families of degree `n`. -/
structure IsTensorProduct (M : DifferentialGradedModule.{t, a, w} A)
    (N : DifferentialGradedBimodule.{t, a, z} A B)
    (T : DifferentialGradedModule.{t, a, s} B) where
  /-- The universal multiplication map `M^i × N^j → T^{i + j}` on local sections. -/
  tmul (i j : ℤ) (U : Cᵒᵖ) :
    (M.complex.X i).val.obj U →+ (N.complex.X j).val.obj U →+ (T.complex.X (i + j)).val.obj U
  /-- The multiplication is linear over the sheaf of rings in the first variable. -/
  tmul_smul_left (i j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) :
    tmul i j U (r • x) y = r • tmul i j U x y
  /-- The multiplication is linear over the sheaf of rings in the second variable. -/
  tmul_smul_right (i j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) :
    tmul i j U x (r • y) = r • tmul i j U x y
  /-- The multiplication commutes with restriction. -/
  tmul_naturality (i j : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) :
    (T.complex.X (i + j)).val.map g (tmul i j U x y) =
      tmul i j V ((M.complex.X i).val.map g x) ((N.complex.X j).val.map g y)
  /-- The multiplication is `A`-balanced: `x a ⊗ y = x ⊗ a y`. -/
  tmul_balanced (i p j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
      (a : (A.complex.X p).val.obj U) (y : (N.complex.X j).val.obj U) :
    HEq (tmul (i + p) j U ((M.mul i p).app U x a) y)
      (tmul i (p + j) U x ((N.leftMul p j).app U a y))
  /-- The right `B`-action on `T` is `(x ⊗ y) b = x ⊗ y b`. -/
  tmul_rightMul (i j p : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) (b : (B.complex.X p).val.obj U) :
    HEq ((T.mul (i + j) p).app U (tmul i j U x y) b)
      (tmul i (j + p) U x ((N.rightMul j p).app U y b))
  /-- The differential of `T` obeys the signed Leibniz rule
  `d (x ⊗ y) = d x ⊗ y + (-1)^i x ⊗ d y`. -/
  tmul_d (i j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
      (y : (N.complex.X j).val.obj U) :
    (T.complex.d (i + j) (i + j + 1)).val.app U (tmul i j U x y) =
      gradedCast (fun q ↦ (T.complex.X q).val.obj U) (add_right_comm i 1 j)
          (tmul (i + 1) j U ((M.complex.d i (i + 1)).val.app U x) y) +
        (Int.negOnePow i : ℤ) •
          gradedCast (fun q ↦ (T.complex.X q).val.obj U) (add_assoc i j 1).symm
            (tmul i (j + 1) U x ((N.complex.d j (j + 1)).val.app U y))
  /-- Composition with the multiplication map is a bijection from the degree-`n` local
  homomorphisms out of `T` onto the `A`-balanced bilinear families of degree `n`. -/
  universal (L : DifferentialGradedModule.{t, a, s} B) (n : ℤ) (U : C) :
    LocalHom T L n U ≃ LocalBalancedBilinear M N L n U
  /-- The bijection is composition with the multiplication map. -/
  universal_app (L : DifferentialGradedModule.{t, a, s} B) (n : ℤ) (U : C)
      (f : LocalHom T L n U) (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (universal L n U f).app i j k hijk V x y =
      f.app (i + j) k hijk V (tmul i j (Opposite.op V.left) x y)

namespace IsTensorProduct

variable {M : DifferentialGradedModule.{t, a, w} A}
  {N : DifferentialGradedBimodule.{t, a, z} A B} {T T' : DifferentialGradedModule.{t, a, s} B}

/-- The multiplication map of a tensor product is additive in the first variable. -/
theorem tmul_add_left (hT : IsTensorProduct M N T) (i j : ℤ) (U : Cᵒᵖ)
    (x x' : (M.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    hT.tmul i j U (x + x') y = hT.tmul i j U x y + hT.tmul i j U x' y := by
  rw [map_add]; rfl

/-- The multiplication map of a tensor product is additive in the second variable. -/
theorem tmul_add_right (hT : IsTensorProduct M N T) (i j : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X i).val.obj U) (y y' : (N.complex.X j).val.obj U) :
    hT.tmul i j U x (y + y') = hT.tmul i j U x y + hT.tmul i j U x y' :=
  map_add _ _ _

/-- The multiplication map of a tensor product kills zero in the first variable. -/
theorem tmul_zero_left (hT : IsTensorProduct M N T) (i j : ℤ) (U : Cᵒᵖ)
    (y : (N.complex.X j).val.obj U) :
    hT.tmul i j U 0 y = 0 := by
  rw [map_zero]; rfl

/-- The multiplication map of a tensor product kills zero in the second variable. -/
theorem tmul_zero_right (hT : IsTensorProduct M N T) (i j : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X i).val.obj U) :
    hT.tmul i j U x 0 = 0 :=
  map_zero _

/-- A degree-`n` local homomorphism out of a tensor product is determined by its values on the
image of the multiplication map. -/
theorem localHom_ext (hT : IsTensorProduct M N T) {L : DifferentialGradedModule.{t, a, s} B}
    {n : ℤ} {U : C} {f g : LocalHom T L n U}
    (h : ∀ (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.complex.X i).val.obj (Opposite.op V.left))
      (y : (N.complex.X j).val.obj (Opposite.op V.left)),
      f.app (i + j) k hijk V (hT.tmul i j (Opposite.op V.left) x y) =
        g.app (i + j) k hijk V (hT.tmul i j (Opposite.op V.left) x y)) : f = g :=
  (hT.universal L n U).injective (LocalBalancedBilinear.ext fun i j k hijk V x y => by
    rw [hT.universal_app, hT.universal_app]; exact h i j k hijk V x y)

/-- The multiplication map of a tensor product, read as an `A`-balanced bilinear family of
degree zero over an object of the site. -/
def tmulBalanced (hT : IsTensorProduct M N T) (U : C) : LocalBalancedBilinear M N T 0 U where
  app i j k hijk V := castHom₂ (M.complex.X i) (N.complex.X j) T.complex.X (by omega)
    (Opposite.op V.left) (hT.tmul i j (Opposite.op V.left))
  map_smul_left i j k hijk V r x y := by
    simp only [castHom₂_apply]
    rw [hT.tmul_smul_left, castHom_smul]
  map_smul_right i j k hijk V r x y := by
    simp only [castHom₂_apply]
    rw [hT.tmul_smul_right, castHom_smul]
  naturality i j k hijk {V W} g x y := by
    have e1 := castHom₂_apply (M.complex.X i) (N.complex.X j) T.complex.X
      (show i + j = k by omega) (Opposite.op V.left) (hT.tmul i j (Opposite.op V.left)) x y
    have e2 := castHom₂_apply (M.complex.X i) (N.complex.X j) T.complex.X
      (show i + j = k by omega) (Opposite.op W.left) (hT.tmul i j (Opposite.op W.left))
      ((M.complex.X i).val.map g.left.op x) ((N.complex.X j).val.map g.left.op y)
    rw [e1, castHom_naturality, hT.tmul_naturality]
    exact e2.symm
  balanced i p j k hijk V x a y := by
    simp only [castHom₂_apply]
    exact castHom_heq T.complex.X _ _ _ (hT.tmul_balanced i p j (Opposite.op V.left) x a y)
  map_rightMul i j p k hijk V x y b := by
    simp only [castHom₂_apply]
    rw [mul_app_castHom]
    exact castHom_heq T.complex.X _ _ _
      (hT.tmul_rightMul i j p (Opposite.op V.left) x y b).symm

/-- The values of the balanced bilinear family of a tensor product are the values of its
multiplication map. -/
theorem tmulBalanced_app (hT : IsTensorProduct M N T) (U : C) (i j k : ℤ)
    (hijk : i + j + 0 = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (hT.tmulBalanced U).app i j k hijk V x y =
      castHom T.complex.X (by omega) (Opposite.op V.left)
        (hT.tmul i j (Opposite.op V.left) x y) :=
  castHom₂_apply (M.complex.X i) (N.complex.X j) T.complex.X (by omega) _ _ x y

/-- The degree-zero local homomorphism from one tensor product of `M` and `N` to another
determined by `x ⊗ y ↦ x ⊗ y`. -/
noncomputable def descend (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (U : C) :
    LocalHom T T' 0 U :=
  (hT.universal T' 0 U).symm (hT'.tmulBalanced U)

/-- Composing the comparison of two tensor products of the same pair with the multiplication
map returns the multiplication map of the target. -/
theorem universal_descend (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (U : C) :
    hT.universal T' 0 U (hT.descend hT' U) = hT'.tmulBalanced U :=
  (hT.universal T' 0 U).apply_symm_apply _

/-- The comparison of two tensor products of the same pair sends `x ⊗ y` to `x ⊗ y`. -/
theorem descend_tmul (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (U : C)
    (i j k : ℤ) (hk : i + j + 0 = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (hT.descend hT' U).app (i + j) k hk V (hT.tmul i j (Opposite.op V.left) x y) =
      castHom T'.complex.X (by omega) (Opposite.op V.left)
        (hT'.tmul i j (Opposite.op V.left) x y) := by
  have h := congrArg (fun β => β.app i j k hk V x y) (hT.universal_descend hT' U)
  simpa only [hT.universal_app, hT'.tmulBalanced_app] using h

/-- Composition with the multiplication map commutes with restriction along a morphism of the
site. -/
theorem universal_restrict (hT : IsTensorProduct M N T)
    (L : DifferentialGradedModule.{t, a, s} B) (n : ℤ) {U U' : C} (g : U' ⟶ U)
    (f : LocalHom T L n U) (i j k : ℤ) (hijk : i + j + n = k) (V : Over U')
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (N.complex.X j).val.obj (Opposite.op V.left)) :
    (hT.universal L n U' (f.restrict g)).app i j k hijk V x y =
      (hT.universal L n U f).app i j k hijk (Over.mk (V.hom ≫ g)) x y := by
  rw [hT.universal_app, hT.universal_app]
  rfl

/-- The comparison of two tensor products of the same pair is compatible with restriction along
a morphism of the site. -/
theorem restrict_descend (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T')
    {U U' : C} (g : U' ⟶ U) :
    (hT.descend hT' U).restrict g = hT.descend hT' U' := by
  refine (hT.universal T' 0 U').injective
    (LocalBalancedBilinear.ext fun i j k hijk V x y => ?_)
  rw [hT.universal_restrict T' 0 g (hT.descend hT' U) i j k hijk V x y,
    hT.universal_descend hT', hT.universal_descend hT']
  exact (hT'.tmulBalanced_app U i j k hijk (Over.mk (V.hom ≫ g)) x y).trans
    (hT'.tmulBalanced_app U' i j k hijk V x y).symm

/-- The map on sections over an object of the site given by the comparison of two tensor
products of the same pair. -/
noncomputable def descendSections (hT : IsTensorProduct M N T)
    (hT' : IsTensorProduct M N T') (k : ℤ)
    (U : Cᵒᵖ) : (T.complex.X k).val.obj U →+ (T'.complex.X k).val.obj U :=
  (hT.descend hT' U.unop).app k k (add_zero k) (Over.mk (𝟙 U.unop))

/-- The comparison of two tensor products of the same pair commutes with restriction. -/
theorem descendSections_naturality (hT : IsTensorProduct M N T)
    (hT' : IsTensorProduct M N T') (k : ℤ) {U V : Cᵒᵖ} (γ : U ⟶ V)
    (x : (T.complex.X k).val.obj U) :
    (T'.complex.X k).val.map γ (hT.descendSections hT' k U x) =
      hT.descendSections hT' k V ((T.complex.X k).val.map γ x) := by
  have hA := (hT.descend hT' U.unop).naturality k k (add_zero k)
    (Over.homMk γ.unop (Category.comp_id γ.unop) :
      Over.mk γ.unop ⟶ Over.mk (𝟙 U.unop)) x
  refine hA.trans ?_
  refine (LocalGradedHom.app_mk_congr (hT.descend hT' U.unop).toLocalGradedHom k k (add_zero k)
    (Category.id_comp γ.unop).symm ((T.complex.X k).val.map γ x)).trans ?_
  exact LocalHom.app_congr (hT.restrict_descend hT' γ.unop) k k (add_zero k)
    (Over.mk (𝟙 V.unop)) ((T.complex.X k).val.map γ x)

/-- The degreewise comparison morphism between two tensor products of the same pair. -/
noncomputable def descendHom (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T')
    (k : ℤ) :
    T.complex.X k ⟶ T'.complex.X k where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => hT.descendSections hT' k U x
          map_add' := fun x y => map_add _ x y
          map_smul' := fun r x => (hT.descend hT' U.unop).map_smul k k (add_zero k)
            (Over.mk (𝟙 U.unop)) r x }
      naturality := fun {U V} γ => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        exact (hT.descendSections_naturality hT' k γ x).symm }

/-- The degreewise comparison morphism acts on local sections through the comparison of the
local homomorphisms. -/
theorem descendHom_apply (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (k : ℤ)
    (U : Cᵒᵖ) (x : (T.complex.X k).val.obj U) :
    (hT.descendHom hT' k).val.app U x = hT.descendSections hT' k U x := rfl

/-- The degreewise comparison morphism between two tensor products of the same pair respects
the right `B`-action. -/
theorem descendHom_mul (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (n i : ℤ)
    (U : Cᵒᵖ) (x : (T.complex.X n).val.obj U) (y : (B.complex.X i).val.obj U) :
    (hT.descendHom hT' (n + i)).val.app U ((T.mul n i).app U x y) =
      (T'.mul n i).app U ((hT.descendHom hT' n).val.app U x) y :=
  (hT.descend hT' U.unop).isLinear n n (add_zero n) i (Over.mk (𝟙 U.unop)) x y

/-- The signed Leibniz rule for the multiplication map of a tensor product, with the degree
transports written as maps on local sections. -/
theorem tmul_d_castHom (hT : IsTensorProduct M N T) (i j : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    (T.complex.d (i + j) (i + j + 1)).val.app U (hT.tmul i j U x y) =
      castHom T.complex.X (add_right_comm i 1 j) U
          (hT.tmul (i + 1) j U ((M.complex.d i (i + 1)).val.app U x) y) +
        (Int.negOnePow i : ℤ) • castHom T.complex.X (add_assoc i j 1).symm U
            (hT.tmul i (j + 1) U x ((N.complex.d j (j + 1)).val.app U y)) := by
  rw [hT.tmul_d i j U x y, castHom_apply, castHom_apply]

/-- The comparison of two tensor products of the same pair respects the right `B`-action on
local sections. -/
theorem descend_mul (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (U : C)
    (n i : ℤ) (V : Over U) (x : (T.complex.X n).val.obj (Opposite.op V.left))
    (b : (B.complex.X i).val.obj (Opposite.op V.left)) :
    (hT.descend hT' U).app (n + i) (n + i) (add_zero (n + i)) V
        ((T.mul n i).app (Opposite.op V.left) x b) =
      (T'.mul n i).app (Opposite.op V.left)
        ((hT.descend hT' U).app n n (add_zero n) V x) b :=
  (hT.descend hT' U).isLinear n n (add_zero n) i V x b

/-- The difference `d ∘ φ - φ ∘ d` between the two ways of transporting the differential along
the comparison `φ` of two tensor products of the same pair, as a degree-one local
homomorphism. -/
noncomputable def descendDiff (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T')
    (U : C) : LocalHom T T' 1 U where
  app i j hij V :=
    (homSections (T'.complex.d i j) (Opposite.op V.left)).comp
        ((hT.descend hT' U).app i i (add_zero i) V) -
      ((hT.descend hT' U).app j j (add_zero j) V).comp
        (homSections (T.complex.d i j) (Opposite.op V.left))
  map_smul i j hij V r x := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      (hT.descend hT' U).map_smul, homSections_smul, smul_sub]
  naturality i j hij {V W} q x := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [map_sub_sections]
    simp only [homSections_naturality, (hT.descend hT' U).naturality]
    rfl
  isLinear i j hij p V x b := by
    subst hij
    have hd : i + p + 1 = i + 1 + p := by omega
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      homSections_apply, map_sub]
    rw [hT.descend_mul hT' U i p V x b,
      d_app_castHom T'.complex hd (Opposite.op V.left),
      T'.leibniz_castHom i p (Opposite.op V.left)
        ((hT.descend hT' U).app i i (add_zero i) V x) b,
      d_app_castHom T.complex hd (Opposite.op V.left),
      T.leibniz_castHom i p (Opposite.op V.left) x b]
    simp only [map_add, map_zsmul, castHom_castHom, castHom_self]
    rw [LocalGradedHom.app_castHom (hT.descend hT' U).toLocalGradedHom
        ((add_assoc i p 1).symm.trans hd) V _,
      hT.descend_mul hT' U (i + 1) p V
        ((T.complex.d i (i + 1)).val.app (Opposite.op V.left) x) b,
      hT.descend_mul hT' U i (p + 1) V x
        ((B.complex.d p (p + 1)).val.app (Opposite.op V.left) b)]
    abel

/-- The value on a local section of the difference of the two ways of transporting the
differential along the comparison of two tensor products of the same pair. -/
theorem descendDiff_app (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (U : C)
    (i j : ℤ) (hij : i + 1 = j) (V : Over U)
    (x : (T.complex.X i).val.obj (Opposite.op V.left)) :
    (hT.descendDiff hT' U).app i j hij V x =
      (T'.complex.d i j).val.app (Opposite.op V.left)
          ((hT.descend hT' U).app i i (add_zero i) V x) -
        (hT.descend hT' U).app j j (add_zero j) V
          ((T.complex.d i j).val.app (Opposite.op V.left) x) := rfl

/-- The comparison of two tensor products of the same pair commutes with the differentials: the
difference of the two ways of transporting the differential vanishes, because it is a local
homomorphism killing every `x ⊗ y`. -/
theorem descendDiff_eq_zero (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T')
    (U : C) : hT.descendDiff hT' U = LocalHom.zero T T' 1 U := by
  refine hT.localHom_ext fun i j k hijk V x y => ?_
  rw [LocalHom.zero_app, hT.descendDiff_app hT' U (i + j) k hijk V,
    hT.descend_tmul hT' U i j (i + j) (add_zero (i + j)) V x y]
  simp only [castHom_self]
  rw [d_app_castHom T'.complex hijk (Opposite.op V.left),
    hT'.tmul_d_castHom i j (Opposite.op V.left) x y,
    d_app_castHom T.complex hijk (Opposite.op V.left),
    hT.tmul_d_castHom i j (Opposite.op V.left) x y]
  simp only [map_add, map_zsmul, castHom_castHom]
  rw [LocalGradedHom.app_castHom (hT.descend hT' U).toLocalGradedHom
      ((add_right_comm i 1 j).trans hijk) V _,
    LocalGradedHom.app_castHom (hT.descend hT' U).toLocalGradedHom
      ((add_assoc i j 1).symm.trans hijk) V _,
    hT.descend_tmul hT' U (i + 1) j (i + 1 + j) (add_zero (i + 1 + j)) V _ y,
    hT.descend_tmul hT' U i (j + 1) (i + (j + 1)) (add_zero (i + (j + 1))) V x _]
  simp only [castHom_self]
  abel

/-- The degreewise comparison morphisms between two tensor products of the same pair commute
with the differentials. -/
theorem descendHom_comm (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T')
    (i j : ℤ) (hij : i + 1 = j) :
    hT.descendHom hT' i ≫ T'.complex.d i j = T.complex.d i j ≫ hT.descendHom hT' j := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  have h := LocalHom.app_congr (hT.descendDiff_eq_zero hT' U.unop) i j hij
    (Over.mk (𝟙 U.unop)) x
  rw [LocalHom.zero_app] at h
  exact sub_eq_zero.mp h

/-- The comparison morphism between two tensor products of the same pair, as a homomorphism of
right differential graded `B`-modules. -/
noncomputable def descendDgHom (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') :
    T ⟶ T' where
  toHomologicalComplex :=
    { f := fun k => hT.descendHom hT' k
      comm' := fun i j hij => hT.descendHom_comm hT' i j hij }
  map_mul n i U x y := hT.descendHom_mul hT' n i U x y

/-- The two comparisons between two tensor products of the same pair are inverse to one another
as local homomorphisms. -/
theorem descend_comp (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (U : C) :
    (hT.descend hT' U).comp (hT'.descend hT U) (add_zero 0) = LocalHom.id T U := by
  refine hT.localHom_ext fun i j k hijk V x y => ?_
  rw [LocalHom.comp_app (hT.descend hT' U) (hT'.descend hT U) (add_zero 0)
      (add_zero (i + j)) hijk V (hT.tmul i j (Opposite.op V.left) x y),
    hT.descend_tmul hT' U i j (i + j) (add_zero (i + j)) V x y]
  simp only [castHom_self]
  rw [LocalHom.id_app]
  exact hT'.descend_tmul hT U i j k hijk V x y

/-- The two degreewise comparison morphisms between two tensor products of the same pair are
inverse to one another. -/
theorem descendHom_comp (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') (k : ℤ) :
    hT.descendHom hT' k ≫ hT'.descendHom hT k = 𝟙 (T.complex.X k) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  have h := LocalHom.app_congr (hT.descend_comp hT' U.unop) k k (add_zero k)
    (Over.mk (𝟙 U.unop)) x
  rw [LocalHom.comp_app (hT.descend hT' U.unop) (hT'.descend hT U.unop) (add_zero 0)
      (add_zero k) (add_zero k) (Over.mk (𝟙 U.unop)) x, LocalHom.id_app, castHom_self] at h
  exact h

/-- Two right differential graded `B`-modules which are both the tensor product `M ⊗_A N` of a
right differential graded `A`-module `M` with a differential graded `(A, B)`-bimodule `N` are
isomorphic, by the canonical isomorphism determined by `x ⊗ y ↦ x ⊗ y`. -/
noncomputable def uniqueIso (hT : IsTensorProduct M N T) (hT' : IsTensorProduct M N T') :
    T ≅ T' where
  hom := hT.descendDgHom hT'
  inv := hT'.descendDgHom hT
  hom_inv_id := DifferentialGradedModule.Hom.ext fun k => hT.descendHom_comp hT' k
  inv_hom_id := DifferentialGradedModule.Hom.ext fun k => hT'.descendHom_comp hT k

end IsTensorProduct

/-- The tensor product with a fixed differential graded `(A, B)`-bimodule `N` for all right
differential graded `A`-modules at once: a functor
`- ⊗_A N : Mod^dg(A, d) ⥤ Mod^dg(B, d)` whose values are tensor products, together with the
description of its action on morphisms as `x ⊗ y ↦ f x ⊗ y`. -/
structure TensorFunctorData (A B : DifferentialGradedAlgebra.{t, a} R)
    (N : DifferentialGradedBimodule.{t, a, z} A B) where
  /-- The tensor product functor `- ⊗_A N`. -/
  functor : DifferentialGradedModule.{t, a, w} A ⥤ DifferentialGradedModule.{t, a, s} B
  /-- Its value at `M` is a tensor product `M ⊗_A N`. -/
  isTensorProduct (M : DifferentialGradedModule.{t, a, w} A) :
    IsTensorProduct M N (functor.obj M)
  /-- On local sections, the functor sends a homomorphism `f` to the map determined by
  `x ⊗ y ↦ f x ⊗ y`. -/
  map_spec {M M' : DifferentialGradedModule.{t, a, w} A} (f : M ⟶ M') (i j : ℤ) (U : Cᵒᵖ)
      (x : (M.complex.X i).val.obj U) (y : (N.complex.X j).val.obj U) :
    ((functor.map f).toHomologicalComplex.f (i + j)).val.app U
        ((isTensorProduct M).tmul i j U x y) =
      (isTensorProduct M').tmul i j U ((f.toHomologicalComplex.f i).val.app U x) y

/-- Two tensor product functors with the same bimodule `N` agree up to canonical isomorphism at
every right differential graded `A`-module. -/
noncomputable def TensorFunctorData.uniqueIso
    {N : DifferentialGradedBimodule.{t, a, z} A B}
    (D D' : TensorFunctorData A B N) (M : DifferentialGradedModule.{t, a, w} A) :
    D.functor.obj M ≅ D'.functor.obj M :=
  (D.isTensorProduct M).uniqueIso (D'.isTensorProduct M)

end SheafOfModules

end
