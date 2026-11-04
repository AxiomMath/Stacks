module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHom

/-!
# Tensor product for sheaves of graded modules

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` and `B` be sheaves of graded
`R`-algebras, let `M` be a right graded `A`-module and let `N` be a graded `(A, B)`-bimodule.
The tensor product `M ⊗_A N` is the graded sheaf of `R`-modules whose degree-`k` part is built
from `⨁_{i + j = k} M^i ⊗_R N^j` by imposing the relations `x b ⊗ y = x ⊗ b y`; it is a right
graded `B`-module by `(x ⊗ y) b = x ⊗ y b`.

This file pins that module down by its universal property: an `A`-balanced bilinear family of
degree `n` out of `M` and `N` is the same thing as a degree-`n` homomorphism of right graded
`B`-modules out of `M ⊗_A N`. The existence of such a module is not asserted here.

## Main definitions

* `SheafOfModules.GradedLocalBalanced` is an `A`-balanced bilinear family of degree `n` over an
  object `U` of the site: maps `M^i|_U × N^j|_U → L^{i + j + n}|_U` which are bilinear over the
  sheaf of rings, compatible with restriction, `A`-balanced (`x b ⊗ y` and `x ⊗ b y` have the
  same image) and `B`-linear in the second variable; `SheafOfModules.GradedGlobalBalanced` is
  the same datum over the whole site and `SheafOfModules.GradedGlobalBalanced.toLocal`
  restricts one to a slice site.
* `SheafOfModules.IsGradedTensorProduct` says that a right graded `B`-module `T` is the tensor
  product `M ⊗_A N`: it carries a universal `A`-balanced bilinear map `tmul`, the right
  `B`-action on `T` is `(x ⊗ y) b = x ⊗ y b`, and composing a degree-`n` local homomorphism out
  of `T` with `tmul` is a bijection onto the `A`-balanced bilinear families of degree `n`.

## Main results

* `SheafOfModules.GradedLocalBalanced.ext` and `SheafOfModules.GradedGlobalBalanced.ext`: a
  balanced bilinear family is determined by its values on local sections.
* `SheafOfModules.IsGradedTensorProduct.localHom_ext`: two degree-`n` local homomorphisms out of
  a tensor product which agree on the image of `tmul` are equal.
* `SheafOfModules.IsGradedTensorProduct.universal_restrict` and `universal_symm_restrict`: the
  universal bijection is compatible with restriction along a morphism of the site.

## Implementation notes

The tensor product cannot be written down by a formula here: the monoidal structure on
presheaves of modules is defined only over a presheaf of *commutative* rings, and sheaves of
modules carry limits, colimits, abelianness and change of rings but nothing monoidal. So, as for
the internal hom, the object is pinned by a universal property instead. The datum `tmul` is
given on local sections over the objects of the site, and the universal property is stated over
each object `U` separately, in terms of the degree-`n` local homomorphisms of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedInternalHom.lean`; this pins the restriction
of `T` to each slice site, which is what makes the characterisation local. The material below is
the undifferentiated analogue of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensor.lean`.

Degrees are carried in two different ways, each chosen so that no formula needs a heterogeneous
equality. The target degree of `tmul` is `i + j` on the nose, as for the two actions of a graded
bimodule, so the associativity-style clauses `tmul_balanced` and `tmul_rightMul` are stated with
`HEq`, exactly as for those actions. The target degree of a balanced bilinear *family* is
instead an independent degree `k` together with a proof of `i + j + n = k`, as for the cochains
of `CochainComplex.HomComplex`, which is what lets the universal property and its consequences
be stated without transports.

The test module of the universal property lies in the same module universe as `T`, because a
structure field cannot quantify over a universe. The base is an arbitrary sheaf of rings on an
arbitrary site rather than the structure sheaf of a ringed site, and the universes of the site,
the ring, the algebras, the module `M` and the bimodule `N` are otherwise independent; a ringed
site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
-/

@[expose] public section

open CategoryTheory

universe t a w z s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- An `A`-balanced bilinear family of degree `n` over an object `U` of the site, from a right
graded `A`-module `M` and a graded `(A, B)`-bimodule `N` to a right graded `B`-module `L`: maps
`M^i|_U × N^j|_U → L^{i + j + n}|_U` which are bilinear over the sheaf of rings, compatible with
restriction, `A`-balanced and `B`-linear in the second variable. -/
@[stacks 0FR2 "local balanced bilinear families out of a graded module and a bimodule"]
structure GradedLocalBalanced (M : GradedModule.{t, a, w} A) (N : GradedBimodule.{t, a, z} A B)
    (L : GradedModule.{t, a, s} B) (n : ℤ) (U : C) where
  /-- The biadditive map on sections over an object `V ⟶ U` of the slice site, from degrees `i`
  and `j` to degree `k`, where `i + j + n = k`. -/
  app (i j k : ℤ) (hijk : i + j + n = k) (V : Over U) :
    (M.piece i).val.obj (Opposite.op V.left) →+
      (N.piece j).val.obj (Opposite.op V.left) →+
        (L.piece k).val.obj (Opposite.op V.left)
  /-- The maps are linear over the sheaf of rings in the first variable. -/
  map_smul_left (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (r : R.obj.obj (Opposite.op V.left))
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (y : (N.piece j).val.obj (Opposite.op V.left)) :
    app i j k hijk V (r • x) y = r • app i j k hijk V x y
  /-- The maps are linear over the sheaf of rings in the second variable. -/
  map_smul_right (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (r : R.obj.obj (Opposite.op V.left))
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (y : (N.piece j).val.obj (Opposite.op V.left)) :
    app i j k hijk V x (r • y) = r • app i j k hijk V x y
  /-- The maps commute with restriction inside the slice site. -/
  naturality (i j k : ℤ) (hijk : i + j + n = k) {V W : Over U} (g : W ⟶ V)
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (y : (N.piece j).val.obj (Opposite.op V.left)) :
    (L.piece k).val.map g.left.op (app i j k hijk V x y) =
      app i j k hijk W ((M.piece i).val.map g.left.op x)
        ((N.piece j).val.map g.left.op y)
  /-- The maps are `A`-balanced: `x b ⊗ y` and `x ⊗ b y` have the same image. -/
  balanced (i p j k : ℤ) (hijk : i + p + j + n = k) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (b : (A.piece p).val.obj (Opposite.op V.left))
      (y : (N.piece j).val.obj (Opposite.op V.left)) :
    app (i + p) j k hijk V (M.smul i p (Opposite.op V.left) x b) y =
      app i (p + j) k (by omega) V x ((N.leftMul p j).app (Opposite.op V.left) b y)
  /-- The maps are `B`-linear in the second variable. -/
  map_rightMul (i j p k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (y : (N.piece j).val.obj (Opposite.op V.left))
      (b : (B.piece p).val.obj (Opposite.op V.left)) :
    app i (j + p) (k + p) (by omega) V x ((N.rightMul j p).app (Opposite.op V.left) y b) =
      L.smul k p (Opposite.op V.left) (app i j k hijk V x y) b

namespace GradedLocalBalanced

variable {M : GradedModule.{t, a, w} A} {N : GradedBimodule.{t, a, z} A B}
  {L : GradedModule.{t, a, s} B}

/-- A balanced bilinear family is determined by its values on local sections. -/
@[ext]
theorem ext {n : ℤ} {U : C} {β γ : GradedLocalBalanced M N L n U}
    (h : ∀ (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (y : (N.piece j).val.obj (Opposite.op V.left)),
      β.app i j k hijk V x y = γ.app i j k hijk V x y) : β = γ := by
  cases β
  cases γ
  congr
  ext i j k hijk V x y
  exact h i j k hijk V x y

/-- The value of a balanced bilinear family over an object of the slice site depends only on
the structure morphism of that object. -/
theorem app_mk_congr {n : ℤ} {U U' : C} (β : GradedLocalBalanced M N L n U) (i j k : ℤ)
    (hijk : i + j + n = k) {g g' : U' ⟶ U} (hg : g = g')
    (x : (M.piece i).val.obj (Opposite.op U'))
    (y : (N.piece j).val.obj (Opposite.op U')) :
    β.app i j k hijk (Over.mk g) x y = β.app i j k hijk (Over.mk g') x y := by
  subst hg
  rfl

/-- A balanced bilinear family evaluated over the terminal object of a slice site is its value
over the base. -/
theorem app_top {n : ℤ} {U : C} (β : GradedLocalBalanced M N L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U) (x : (M.piece i).val.obj (Opposite.op V.left))
    (y : (N.piece j).val.obj (Opposite.op V.left)) :
    β.app i j k hijk (Over.mk ((Over.mk (𝟙 V.left)).hom ≫ V.hom))
        ((M.piece i).val.map (Over.mk (𝟙 V.left)).hom.op x) y =
      β.app i j k hijk V x y :=
  (congrArg (fun u : (N.piece j).val.obj (Opposite.op V.left) =>
      β.app i j k hijk (Over.mk ((Over.mk (𝟙 V.left)).hom ≫ V.hom))
        ((M.piece i).val.map (Over.mk (𝟙 V.left)).hom.op x) u)
    (map_top_sections (N.piece j) V.left y).symm).trans
      ((β.naturality i j k hijk
        (Over.homMk (𝟙 V.left) rfl :
          Over.mk ((Over.mk (𝟙 V.left)).hom ≫ V.hom) ⟶ V) x y).symm.trans
          (map_top_sections (L.piece k) V.left _))

/-- Restrict a balanced bilinear family along a morphism `U' ⟶ U` of the site, by viewing the
objects of the slice site over `U'` as objects over `U`. -/
def restrict {n : ℤ} {U U' : C} (g : U' ⟶ U) (β : GradedLocalBalanced M N L n U) :
    GradedLocalBalanced M N L n U' where
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

/-- The restriction of `β` along `g` evaluates on an object `V` over `U'` as `β` evaluates on
`V` regarded as an object over `U`. -/
@[simp]
theorem restrict_app {n : ℤ} {U U' : C} (g : U' ⟶ U) (β : GradedLocalBalanced M N L n U)
    (i j k : ℤ) (hijk : i + j + n = k) (V : Over U')
    (x : (M.piece i).val.obj (Opposite.op V.left))
    (y : (N.piece j).val.obj (Opposite.op V.left)) :
    (β.restrict g).app i j k hijk V x y = β.app i j k hijk (Over.mk (V.hom ≫ g)) x y := rfl

end GradedLocalBalanced

/-- An `A`-balanced bilinear family of degree `n` over the whole site: maps
`M^i × N^j → L^{i + j + n}` on sections which are bilinear over the sheaf of rings, compatible
with restriction, `A`-balanced and `B`-linear in the second variable. -/
@[stacks 0FR2 "balanced bilinear families out of a graded module and a bimodule"]
structure GradedGlobalBalanced (M : GradedModule.{t, a, w} A) (N : GradedBimodule.{t, a, z} A B)
    (L : GradedModule.{t, a, s} B) (n : ℤ) where
  /-- The biadditive map on sections over an object of the site, from degrees `i` and `j` to
  degree `k`, where `i + j + n = k`. -/
  app (i j k : ℤ) (hijk : i + j + n = k) (U : Cᵒᵖ) :
    (M.piece i).val.obj U →+ (N.piece j).val.obj U →+ (L.piece k).val.obj U
  /-- The maps are linear over the sheaf of rings in the first variable. -/
  map_smul_left (i j k : ℤ) (hijk : i + j + n = k) (U : Cᵒᵖ) (r : R.obj.obj U)
      (x : (M.piece i).val.obj U) (y : (N.piece j).val.obj U) :
    app i j k hijk U (r • x) y = r • app i j k hijk U x y
  /-- The maps are linear over the sheaf of rings in the second variable. -/
  map_smul_right (i j k : ℤ) (hijk : i + j + n = k) (U : Cᵒᵖ) (r : R.obj.obj U)
      (x : (M.piece i).val.obj U) (y : (N.piece j).val.obj U) :
    app i j k hijk U x (r • y) = r • app i j k hijk U x y
  /-- The maps commute with restriction. -/
  naturality (i j k : ℤ) (hijk : i + j + n = k) {U V : Cᵒᵖ} (g : U ⟶ V)
      (x : (M.piece i).val.obj U) (y : (N.piece j).val.obj U) :
    (L.piece k).val.map g (app i j k hijk U x y) =
      app i j k hijk V ((M.piece i).val.map g x) ((N.piece j).val.map g y)
  /-- The maps are `A`-balanced: `x b ⊗ y` and `x ⊗ b y` have the same image. -/
  balanced (i p j k : ℤ) (hijk : i + p + j + n = k) (U : Cᵒᵖ)
      (x : (M.piece i).val.obj U) (b : (A.piece p).val.obj U)
      (y : (N.piece j).val.obj U) :
    app (i + p) j k hijk U (M.smul i p U x b) y =
      app i (p + j) k (by omega) U x ((N.leftMul p j).app U b y)
  /-- The maps are `B`-linear in the second variable. -/
  map_rightMul (i j p k : ℤ) (hijk : i + j + n = k) (U : Cᵒᵖ)
      (x : (M.piece i).val.obj U) (y : (N.piece j).val.obj U)
      (b : (B.piece p).val.obj U) :
    app i (j + p) (k + p) (by omega) U x ((N.rightMul j p).app U y b) =
      L.smul k p U (app i j k hijk U x y) b

namespace GradedGlobalBalanced

variable {M : GradedModule.{t, a, w} A} {N : GradedBimodule.{t, a, z} A B}
  {L : GradedModule.{t, a, s} B}

/-- A balanced bilinear family over the site is determined by its values on sections. -/
@[ext]
theorem ext {n : ℤ} {β γ : GradedGlobalBalanced M N L n}
    (h : ∀ (i j k : ℤ) (hijk : i + j + n = k) (U : Cᵒᵖ)
      (x : (M.piece i).val.obj U) (y : (N.piece j).val.obj U),
      β.app i j k hijk U x y = γ.app i j k hijk U x y) : β = γ := by
  cases β
  cases γ
  congr
  ext i j k hijk U x y
  exact h i j k hijk U x y

/-- Restrict a balanced bilinear family over the site to the slice site over an object. -/
def toLocal {n : ℤ} (β : GradedGlobalBalanced M N L n) (U : C) :
    GradedLocalBalanced M N L n U where
  app i j k hijk V := β.app i j k hijk (Opposite.op V.left)
  map_smul_left i j k hijk V r x y :=
    β.map_smul_left i j k hijk (Opposite.op V.left) r x y
  map_smul_right i j k hijk V r x y :=
    β.map_smul_right i j k hijk (Opposite.op V.left) r x y
  naturality i j k hijk {_V _W} q x y := β.naturality i j k hijk q.left.op x y
  balanced i p j k hijk V x b y := β.balanced i p j k hijk (Opposite.op V.left) x b y
  map_rightMul i j p k hijk V x y b :=
    β.map_rightMul i j p k hijk (Opposite.op V.left) x y b

/-- The restriction of `β` to the slice site over `U` evaluates on an object `V` over `U` as `β`
evaluates on the underlying object of `V`. -/
@[simp]
theorem toLocal_app {n : ℤ} (β : GradedGlobalBalanced M N L n) (U : C) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U)
    (x : (M.piece i).val.obj (Opposite.op V.left))
    (y : (N.piece j).val.obj (Opposite.op V.left)) :
    (β.toLocal U).app i j k hijk V x y = β.app i j k hijk (Opposite.op V.left) x y := rfl

/-- Restricting `β` to the slice site over `U` and then along `g : U' ⟶ U` gives the restriction
of `β` to the slice site over `U'`. -/
theorem restrict_toLocal {n : ℤ} (β : GradedGlobalBalanced M N L n) {U U' : C} (g : U' ⟶ U) :
    (β.toLocal U).restrict g = β.toLocal U' := rfl

end GradedGlobalBalanced

/-- A right graded `B`-module `T` is the tensor product `M ⊗_A N` of a right graded `A`-module
`M` with a graded `(A, B)`-bimodule `N` when it carries an `A`-balanced bilinear map `tmul` of
degree zero whose right `B`-action is `(x ⊗ y) b = x ⊗ y b` and which is universal: composing a
degree-`n` local homomorphism out of `T` with `tmul` is a bijection onto the `A`-balanced
bilinear families of degree `n`. -/
@[stacks 0FR2 "the graded tensor product, by its universal property"]
structure IsGradedTensorProduct (M : GradedModule.{t, a, w} A)
    (N : GradedBimodule.{t, a, z} A B) (T : GradedModule.{t, a, s} B) where
  /-- The universal multiplication map `M^i × N^j → T^{i + j}` on local sections. -/
  tmul (i j : ℤ) (U : Cᵒᵖ) :
    (M.piece i).val.obj U →+ (N.piece j).val.obj U →+ (T.piece (i + j)).val.obj U
  /-- The multiplication is linear over the sheaf of rings in the first variable. -/
  tmul_smul_left (i j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (M.piece i).val.obj U)
      (y : (N.piece j).val.obj U) :
    tmul i j U (r • x) y = r • tmul i j U x y
  /-- The multiplication is linear over the sheaf of rings in the second variable. -/
  tmul_smul_right (i j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (M.piece i).val.obj U)
      (y : (N.piece j).val.obj U) :
    tmul i j U x (r • y) = r • tmul i j U x y
  /-- The multiplication commutes with restriction. -/
  tmul_naturality (i j : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V) (x : (M.piece i).val.obj U)
      (y : (N.piece j).val.obj U) :
    (T.piece (i + j)).val.map g (tmul i j U x y) =
      tmul i j V ((M.piece i).val.map g x) ((N.piece j).val.map g y)
  /-- The multiplication is `A`-balanced: `x b ⊗ y = x ⊗ b y`. -/
  tmul_balanced (i p j : ℤ) (U : Cᵒᵖ) (x : (M.piece i).val.obj U)
      (b : (A.piece p).val.obj U) (y : (N.piece j).val.obj U) :
    HEq (tmul (i + p) j U (M.smul i p U x b) y)
      (tmul i (p + j) U x ((N.leftMul p j).app U b y))
  /-- The right `B`-action on `T` is `(x ⊗ y) b = x ⊗ y b`. -/
  tmul_rightMul (i j p : ℤ) (U : Cᵒᵖ) (x : (M.piece i).val.obj U)
      (y : (N.piece j).val.obj U) (b : (B.piece p).val.obj U) :
    HEq (T.smul (i + j) p U (tmul i j U x y) b)
      (tmul i (j + p) U x ((N.rightMul j p).app U y b))
  /-- Composition with the multiplication map is a bijection from the degree-`n` local
  homomorphisms out of `T` onto the `A`-balanced bilinear families of degree `n`. -/
  universal (K : GradedModule.{t, a, s} B) (n : ℤ) (U : C) :
    GradedLocalHom T K n U ≃ GradedLocalBalanced M N K n U
  /-- The bijection is composition with the multiplication map. -/
  universal_app (K : GradedModule.{t, a, s} B) (n : ℤ) (U : C) (f : GradedLocalHom T K n U)
      (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (y : (N.piece j).val.obj (Opposite.op V.left)) :
    (universal K n U f).app i j k hijk V x y =
      f.app (i + j) k hijk V (tmul i j (Opposite.op V.left) x y)

namespace IsGradedTensorProduct

variable {M : GradedModule.{t, a, w} A} {N : GradedBimodule.{t, a, z} A B}
  {T : GradedModule.{t, a, s} B}

/-- A degree-`n` local homomorphism out of a tensor product is determined by its values on the
image of the multiplication map. -/
theorem localHom_ext (hT : IsGradedTensorProduct M N T) {K : GradedModule.{t, a, s} B} {n : ℤ}
    {U : C} {f g : GradedLocalHom T K n U}
    (h : ∀ (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (y : (N.piece j).val.obj (Opposite.op V.left)),
      f.app (i + j) k hijk V (hT.tmul i j (Opposite.op V.left) x y) =
        g.app (i + j) k hijk V (hT.tmul i j (Opposite.op V.left) x y)) : f = g :=
  (hT.universal K n U).injective (GradedLocalBalanced.ext fun i j k hijk V x y => by
    rw [hT.universal_app, hT.universal_app]
    exact h i j k hijk V x y)

/-- Composition with the multiplication map commutes with restriction along a morphism of the
site. -/
theorem universal_restrict (hT : IsGradedTensorProduct M N T) (K : GradedModule.{t, a, s} B)
    (n : ℤ) {U U' : C} (g : U' ⟶ U) (f : GradedLocalHom T K n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U')
    (x : (M.piece i).val.obj (Opposite.op V.left))
    (y : (N.piece j).val.obj (Opposite.op V.left)) :
    (hT.universal K n U' (f.restrict g)).app i j k hijk V x y =
      (hT.universal K n U f).app i j k hijk (Over.mk (V.hom ≫ g)) x y := by
  rw [hT.universal_app, hT.universal_app]
  rfl

/-- The inverse of the universal bijection is compatible with restriction along a morphism of
the site. -/
theorem universal_symm_restrict (hT : IsGradedTensorProduct M N T)
    (K : GradedModule.{t, a, s} B) (n : ℤ) {U U' : C} (g : U' ⟶ U)
    (β : GradedLocalBalanced M N K n U) :
    ((hT.universal K n U).symm β).restrict g = (hT.universal K n U').symm (β.restrict g) := by
  refine (hT.universal K n U').injective (GradedLocalBalanced.ext fun i j k hijk V x y => ?_)
  rw [hT.universal_restrict K n g ((hT.universal K n U).symm β) i j k hijk V x y,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, GradedLocalBalanced.restrict_app]

end IsGradedTensorProduct

end SheafOfModules

end
