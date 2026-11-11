module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Internal hom for sheaves of graded modules

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` be a sheaf of graded `R`-algebras and
let `M` and `L` be right graded `A`-modules. The graded internal hom is the graded sheaf of
`R`-modules whose degree-`n` part `SheafHom^n_A(M, L)` has as its sections over an object `U` of
the site the maps `M|_U → L|_U` of right graded `A|_U`-modules which are homogeneous of degree
`n`. If `M` is replaced by a graded `(A, B)`-bimodule `N` and `L` is a right graded `B`-module,
then `SheafHom^gr_B(N, L)` carries a right `A`-action, with no signs:

`(f a)(y) = f (a y)`.

This file provides the vocabulary of those local sections, the right `A`-action on them, the
homogeneous homomorphisms of degree `n` in the graded category of right graded modules, and the
predicates saying that a graded sheaf of `R`-modules *is* the internal hom, respectively that a
right graded `A`-module *is* the internal hom of a bimodule together with its `A`-action.

## Main definitions

* `SheafOfModules.GradedLocalHom` is a local section of `SheafHom^n_A(M, L)` over `U`: a
  degree-`n` map `M|_U → L|_U` of right graded `A|_U`-modules, written out as a family of maps
  on sections over the objects `V ⟶ U` of the slice site.
* `SheafOfModules.GradedLocalHom.restrict` restricts such a local section along a morphism of
  the site.
* `SheafOfModules.GradedBimodule.toGradedModule` is the right graded `B`-module underlying a
  graded `(A, B)`-bimodule, and `SheafOfModules.GradedLocalHom.actRight` is the right `A`-action
  `(f a)(y) = f (a y)` on the local sections of `SheafHom^gr_B(N, L)`.
* `SheafOfModules.GradedHomOfDegree` is a homomorphism of right graded `A`-modules homogeneous
  of degree `n`, i.e. an element of `Hom^n` in the graded category of right graded modules;
  `SheafOfModules.GradedHomOfDegree.toLocal` restricts one to the slice site over an object, and
  `SheafOfModules.GradedHomOfDegree.ofLocal` assembles a compatible family of local sections
  into one.
* `SheafOfModules.IsGradedSheafHom` says that a graded sheaf of `R`-modules `G` is
  `SheafHom^gr_A(M, L)`: its degree-`n` sections over `U` are the degree-`n` local
  homomorphisms `M|_U → L|_U`, additively, `R`-linearly and compatibly with restriction.
* `SheafOfModules.IsGradedInternalHom` says that a right graded `A`-module `H` is
  `SheafHom^gr_B(N, L)` for a graded `(A, B)`-bimodule `N`: its underlying graded sheaf is that
  internal hom and its right `A`-action is `SheafOfModules.GradedLocalHom.actRight`. The right
  graded `A`-module `SheafHom^gr_B(N, L)` of [Stacks, Tag 0FR4] is constructed as
  `SheafOfModules.gradedSheafHomModule` in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedInternalHomModule.lean`.

## Main results

* `SheafOfModules.GradedLocalHom.ext` and `SheafOfModules.GradedHomOfDegree.ext`: a local
  section, respectively a homogeneous homomorphism, is determined by its values on local
  sections.
* `SheafOfModules.GradedHomOfDegree.toLocal_ofLocal`: assembling a compatible family of local
  sections and restricting again returns the family.
* `SheafOfModules.IsGradedSheafHom.symm_add`, `symm_smul` and `symm_naturality`: naming a local
  homomorphism by a section of the internal hom is additive, `R`-linear and compatible with
  restriction.

## Implementation notes

This file provides the vocabulary only. The internal hom itself is constructed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedInternalHomSheaf.lean`, over a base whose
rings of sections are commutative, where the degree-`n` local homomorphisms are shown to form a
sheaf of modules (`SheafOfModules.gradedLocalHomSheaf`); that file also gives the composition
map and the identification of `Hom_{Mod^gr(A)}` with global sections, which together are the
content of [Stacks, Tag 0FR3]. The predicate `SheafOfModules.IsGradedSheafHom` below says that
a graded sheaf of `R`-modules *is* the internal hom when its local sections are the local
homomorphisms, additively and `R`-linearly and compatibly with restriction; this determines it
up to canonical isomorphism, and the constructed sheaf satisfies it
(`SheafOfModules.isGradedSheafHom_gradedSheafHom`). This is the same device as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInternalHom.lean`, of which the
material below is the undifferentiated analogue.

Restriction of a sheaf of modules to a slice site is not available either, so a degree-`n` map
`M|_U → L|_U` is written out directly as a family of maps on sections over the objects `V ⟶ U`
of the slice site, which is the same datum.

Degrees are carried in the form `(i, j, hij : i + n = j)` used by the cochains of
`CochainComplex.HomComplex`. The point is that the intermediate degrees of every formula can
then be chosen so that both sides are sections of one and the same sheaf, and the only
heterogeneous equalities left are the ones already present in the laws of a graded module or a
graded bimodule, whose multiplication maps land in `piece (n + m)` on the nose.

A `GradedHomOfDegree` is a family of *morphisms of sheaves of modules* `M^i ⟶ L^{i + n}`,
matching `SheafOfModules.GradedModule.Hom`, which forces `M` and `L` into one module universe.
The universes of the site, of the sheaf of rings, of the graded algebras and of each individual
module are otherwise independent, and the base is an arbitrary sheaf of rings on an arbitrary
site rather than the structure sheaf of a ringed site; a ringed site `X` is the case
`R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
* [Stacks Project, Tag 0FR3](https://stacks.math.columbia.edu/tag/0FR3)
* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
-/

@[expose] public section

open CategoryTheory

universe t a w z s h v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- Transport along an equality of degrees identifies two heterogeneously equal local
sections. -/
theorem castHom_congr_heq (X : ℤ → SheafOfModules.{w} R) {i j k : ℤ} (hi : i = k) (hj : j = k)
    (U : Cᵒᵖ) {x : (X i).val.obj U} {y : (X j).val.obj U} (hxy : HEq x y) :
    castHom X hi U x = castHom X hj U y := by
  subst hi
  subst hj
  exact eq_of_heq hxy

/-- Restriction of a local section along the structure morphism of the terminal object of a
slice site does nothing. -/
theorem map_top_sections (X : SheafOfModules.{w} R) (U : C) (x : X.val.obj (Opposite.op U)) :
    X.val.map (Over.mk (𝟙 U)).hom.op x = x := by
  change X.val.map (𝟙 (Opposite.op U)) x = x
  simp only [PresheafOfModules.map_id]
  rfl

/-- Restriction of a local section of the sheaf of rings along the structure morphism of the
terminal object of a slice site does nothing. -/
theorem ring_map_top (U : C) (r : R.obj.obj (Opposite.op U)) :
    R.obj.map (Over.mk (𝟙 U)).hom.op r = r := by
  change R.obj.map (𝟙 (Opposite.op U)) r = r
  simp

/-- The right graded `B`-module underlying a graded `(A, B)`-bimodule, obtained by forgetting
the left `A`-action. -/
def GradedBimodule.toGradedModule (N : GradedBimodule.{t, a, z} A B) :
    GradedModule.{t, a, z} B where
  piece := N.piece
  smul n i U := (N.rightMul n i).app U
  smul_smul_left n i U r x y := (N.rightMul n i).map_smul_left U r x y
  smul_smul_right n i U r x y := (N.rightMul n i).map_smul_right U r x y
  smul_naturality n i {_U _V} f x y := (N.rightMul n i).naturality f x y
  smul_mul n i j U x y z := N.right_assoc n i j U x y z
  smul_one n U x := N.one_right n U x

/-- The pieces of the right graded module underlying a graded bimodule are those of the
bimodule. -/
@[simp]
theorem GradedBimodule.toGradedModule_piece (N : GradedBimodule.{t, a, z} A B) (n : ℤ) :
    N.toGradedModule.piece n = N.piece n := rfl

/-- The action of the right graded module underlying a graded bimodule is the right
multiplication of the bimodule. -/
theorem GradedBimodule.toGradedModule_smul (N : GradedBimodule.{t, a, z} A B) (n i : ℤ)
    (U : Cᵒᵖ) : N.toGradedModule.smul n i U = (N.rightMul n i).app U := rfl

/-- A local section of `SheafHom^n_A(M, L)` over an object `U` of the site: a map
`M|_U → L|_U` of right graded `A|_U`-modules homogeneous of degree `n`, written out as a family
of maps on sections over the objects `V ⟶ U` of the slice site. This is only the type of local
sections; the sheaf of `O`-modules they form, with the rest of Stacks 0FR3, is
`SheafOfModules.gradedLocalHomSheaf` and its companions in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedInternalHomSheaf.lean`. -/
structure GradedLocalHom (M : GradedModule.{t, a, w} A) (L : GradedModule.{t, a, z} A) (n : ℤ)
    (U : C) where
  /-- The map on sections over an object `V ⟶ U` of the slice site, from degree `i` to degree
  `j`, where `i + n = j`. -/
  app (i j : ℤ) (hij : i + n = j) (V : Over U) :
    (M.piece i).val.obj (Opposite.op V.left) →+ (L.piece j).val.obj (Opposite.op V.left)
  /-- The maps are linear over the sheaf of rings. -/
  map_smul (i j : ℤ) (hij : i + n = j) (V : Over U) (r : R.obj.obj (Opposite.op V.left))
      (x : (M.piece i).val.obj (Opposite.op V.left)) :
    app i j hij V (r • x) = r • app i j hij V x
  /-- The maps commute with restriction inside the slice site. -/
  naturality (i j : ℤ) (hij : i + n = j) {V W : Over U} (g : W ⟶ V)
      (x : (M.piece i).val.obj (Opposite.op V.left)) :
    (L.piece j).val.map g.left.op (app i j hij V x) =
      app i j hij W ((M.piece i).val.map g.left.op x)
  /-- The maps are `A|_U`-linear: `f (x b) = f (x) b`. -/
  map_mul (i j : ℤ) (hij : i + n = j) (p : ℤ) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left))
      (b : (A.piece p).val.obj (Opposite.op V.left)) :
    app (i + p) (j + p) (by omega) V (M.smul i p (Opposite.op V.left) x b) =
      L.smul j p (Opposite.op V.left) (app i j hij V x) b

namespace GradedLocalHom

variable {M : GradedModule.{t, a, w} A} {L : GradedModule.{t, a, z} A}

/-- A local section of the graded internal hom is determined by its values on local
sections. -/
@[ext]
theorem ext {n : ℤ} {U : C} {f g : GradedLocalHom M L n U}
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left)),
      f.app i j hij V x = g.app i j hij V x) : f = g := by
  cases f with
  | mk fapp fsmul fnat fmul =>
    cases g with
    | mk gapp gsmul gnat gmul =>
      have happ : fapp = gapp := by
        funext i j hij V
        exact AddMonoidHom.ext fun x => h i j hij V x
      subst happ
      rfl

/-- Two values of a local section of the graded internal hom on heterogeneously equal local
sections of the source agree. -/
theorem app_congr_heq {n : ℤ} {U : C} (f : GradedLocalHom M L n U) {i i' j : ℤ}
    (hij : i + n = j) (hij' : i' + n = j) (V : Over U)
    {x : (M.piece i).val.obj (Opposite.op V.left)}
    {y : (M.piece i').val.obj (Opposite.op V.left)} (hxy : HEq x y) :
    f.app i j hij V x = f.app i' j hij' V y := by
  obtain rfl : i = i' := by omega
  obtain rfl := eq_of_heq hxy
  rfl

/-- The value of a local section of the graded internal hom over an object of the slice site
depends only on the structure morphism of that object. -/
theorem app_mk_congr {n : ℤ} {U U' : C} (f : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j)
    {g g' : U' ⟶ U} (hg : g = g') (x : (M.piece i).val.obj (Opposite.op U')) :
    f.app i j hij (Over.mk g) x = f.app i j hij (Over.mk g') x := by
  subst hg
  rfl

/-- Restrict a local section of the graded internal hom along a morphism `U' ⟶ U` of the site,
by viewing the objects of the slice site over `U'` as objects over `U`. -/
def restrict {n : ℤ} {U U' : C} (g : U' ⟶ U) (f : GradedLocalHom M L n U) :
    GradedLocalHom M L n U' where
  app i j hij V := f.app i j hij (Over.mk (V.hom ≫ g))
  map_smul i j hij V r x := f.map_smul i j hij (Over.mk (V.hom ≫ g)) r x
  naturality i j hij {V W} q x :=
    f.naturality i j hij (V := Over.mk (V.hom ≫ g)) (W := Over.mk (W.hom ≫ g))
      (Over.homMk q.left (show q.left ≫ V.hom ≫ g = W.hom ≫ g by
        rw [← Category.assoc, Over.w q])) x
  map_mul i j hij p V x b := f.map_mul i j hij p (Over.mk (V.hom ≫ g)) x b

/-- The value of the restriction of `f` along `g` on an object `V` over `U'` is the value of `f`
on `V` viewed as an object over `U`. -/
@[simp]
theorem restrict_app {n : ℤ} {U U' : C} (g : U' ⟶ U) (f : GradedLocalHom M L n U) (i j : ℤ)
    (hij : i + n = j) (V : Over U') (x : (M.piece i).val.obj (Opposite.op V.left)) :
    (f.restrict g).app i j hij V x = f.app i j hij (Over.mk (V.hom ≫ g)) x := rfl

end GradedLocalHom

/-- Right multiplication of a local section `f` of `SheafHom^n_B(N, L)` over `U` by a section
`a` of `A^m` over `U`, defined by `(f a)(y) = f (a y)`. This involves no signs.

These are the multiplication maps of [Stacks, Tag 0FR4] on local sections only. The statement of
Stacks 0FR4 that they make `SheafHom^gr_B(N, L)` a right graded `A`-module is
`SheafOfModules.gradedSheafHomModule`, with the laws of the action proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedInternalHomModule.lean`; the functors
`SheafHom^gr_B(N, -)` are there too, and the right graded `B`-module `M ⊗_A N` with its functors
is `SheafOfModules.RelativeTensor.gradedTensorRight` and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedBimoduleTensorFunctor.lean`. -/
noncomputable def GradedLocalHom.actRight {N : GradedBimodule.{t, a, z} A B}
    {L : GradedModule.{t, a, s} B} {n : ℤ} {U : C}
    (f : GradedLocalHom N.toGradedModule L n U) (m : ℤ)
    (a : (A.piece m).val.obj (Opposite.op U)) :
    GradedLocalHom N.toGradedModule L (n + m) U where
  app i j hij V := (f.app (m + i) j (by omega) V).comp
    ((N.leftMul m i).app (Opposite.op V.left) ((A.piece m).val.map V.hom.op a))
  map_smul i j hij V r x :=
    (congrArg (f.app (m + i) j (by omega) V)
        ((N.leftMul m i).map_smul_right (Opposite.op V.left) r
          ((A.piece m).val.map V.hom.op a) x)).trans
      (f.map_smul (m + i) j (by omega) V r _)
  naturality i j hij {V W} q x := by
    have hq : (A.piece m).val.map W.hom.op a =
        (A.piece m).val.map q.left.op ((A.piece m).val.map V.hom.op a) := by
      rw [← (A.piece m).val.map_comp_apply, ← op_comp, Over.w q]
    refine (f.naturality (m + i) j (by omega) q _).trans
      ((congrArg (f.app (m + i) j (by omega) W)
        ((N.leftMul m i).naturality q.left.op ((A.piece m).val.map V.hom.op a) x)).trans ?_)
    exact congrArg (fun c => f.app (m + i) j (by omega) W
      ((N.leftMul m i).app (Opposite.op W.left) c
        ((N.piece i).val.map q.left.op x))) hq.symm
  map_mul i j hij p V x b :=
    (f.app_congr_heq (i := m + (i + p)) (i' := m + i + p) (by omega) (by omega) V
        (N.left_right_assoc m i p (Opposite.op V.left)
          ((A.piece m).val.map V.hom.op a) x b).symm).trans
      (f.map_mul (m + i) j (by omega) p V
        ((N.leftMul m i).app (Opposite.op V.left) ((A.piece m).val.map V.hom.op a) x) b)

/-- The value of `f.actRight m a` on a section `y` is `f (a y)`, with `a` restricted to the object
of the slice site. -/
@[simp]
theorem GradedLocalHom.actRight_app {N : GradedBimodule.{t, a, z} A B}
    {L : GradedModule.{t, a, s} B} {n : ℤ} {U : C} (f : GradedLocalHom N.toGradedModule L n U)
    (m : ℤ) (a : (A.piece m).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + (n + m) = j)
    (V : Over U) (y : (N.piece i).val.obj (Opposite.op V.left)) :
    (f.actRight m a).app i j hij V y =
      f.app (m + i) j (by omega) V
        ((N.leftMul m i).app (Opposite.op V.left) ((A.piece m).val.map V.hom.op a) y) := rfl

/-- A homomorphism of right graded `A`-modules homogeneous of degree `n`: a family of morphisms
`M^i ⟶ L^{i + n}` of sheaves of modules compatible with the right action. These are the
elements of `Hom^n` in the graded category of right graded `A`-modules. -/
@[stacks 0FR1 "homogeneous homomorphisms of degree n of right graded modules"]
structure GradedHomOfDegree (M L : GradedModule.{t, a, w} A) (n : ℤ) where
  /-- The morphism of sheaves of modules from degree `i` to degree `j`, where `i + n = j`. -/
  app (i j : ℤ) (hij : i + n = j) : M.piece i ⟶ L.piece j
  /-- The morphisms are compatible with the right action: `f (x b) = f (x) b`. -/
  map_mul (i j : ℤ) (hij : i + n = j) (p : ℤ) (U : Cᵒᵖ) (x : (M.piece i).val.obj U)
      (b : (A.piece p).val.obj U) :
    (app (i + p) (j + p) (by omega)).val.app U (M.smul i p U x b) =
      L.smul j p U ((app i j hij).val.app U x) b

namespace GradedHomOfDegree

variable {M L : GradedModule.{t, a, w} A}

/-- A homogeneous homomorphism of right graded modules is determined by its components. -/
@[ext]
theorem ext {n : ℤ} {f g : GradedHomOfDegree M L n}
    (h : ∀ (i j : ℤ) (hij : i + n = j), f.app i j hij = g.app i j hij) : f = g := by
  cases f with
  | mk fapp fmul =>
    cases g with
    | mk gapp gmul =>
      have happ : fapp = gapp := by
        funext i j hij
        exact h i j hij
      subst happ
      rfl

/-- Two values of a homogeneous homomorphism on heterogeneously equal local sections of the
source agree. -/
theorem app_congr_heq {n : ℤ} (f : GradedHomOfDegree M L n) {i i' j : ℤ} (hij : i + n = j)
    (hij' : i' + n = j) (U : Cᵒᵖ) {x : (M.piece i).val.obj U} {y : (M.piece i').val.obj U}
    (hxy : HEq x y) :
    (f.app i j hij).val.app U x = (f.app i' j hij').val.app U y := by
  obtain rfl : i = i' := by omega
  obtain rfl := eq_of_heq hxy
  rfl

/-- Restrict a homogeneous homomorphism to the slice site over an object of the site. -/
def toLocal {n : ℤ} (f : GradedHomOfDegree M L n) (U : C) : GradedLocalHom M L n U where
  app i j hij V := homSections (f.app i j hij) (Opposite.op V.left)
  map_smul i j hij V r x := homSections_smul (f.app i j hij) (Opposite.op V.left) r x
  naturality i j hij {_V _W} g x := homSections_naturality (f.app i j hij) g.left.op x
  map_mul i j hij p V x b := f.map_mul i j hij p (Opposite.op V.left) x b

/-- The value of `f.toLocal U` on an object `V` over `U` is the component of `f` on sections over
`V`. -/
@[simp]
theorem toLocal_app {n : ℤ} (f : GradedHomOfDegree M L n) (U : C) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (M.piece i).val.obj (Opposite.op V.left)) :
    (f.toLocal U).app i j hij V x = (f.app i j hij).val.app (Opposite.op V.left) x := rfl

/-- Restricting the local section `f.toLocal U` along `g : U' ⟶ U` gives `f.toLocal U'`. -/
theorem restrict_toLocal {n : ℤ} (f : GradedHomOfDegree M L n) {U U' : C} (g : U' ⟶ U) :
    (f.toLocal U).restrict g = f.toLocal U' := rfl

/-- The map on sections over `U` underlying a compatible family of local sections of the
internal hom, one over each object of the site. -/
def ofLocalSections {n : ℤ} (f : ∀ U : C, GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j)
    (U : Cᵒᵖ) : (M.piece i).val.obj U →+ (L.piece j).val.obj U :=
  (f U.unop).app i j hij (Over.mk (𝟙 U.unop))

/-- Equal local sections have equal values over the terminal object of the slice site. -/
private theorem app_top_congr {n : ℤ} {U : C} {f g : GradedLocalHom M L n U} (h : f = g)
    (i j : ℤ) (hij : i + n = j) (x : (M.piece i).val.obj (Opposite.op U)) :
    f.app i j hij (Over.mk (𝟙 U)) x = g.app i j hij (Over.mk (𝟙 U)) x := by
  rw [h]

/-- A compatible family of local sections of the internal hom commutes with restriction. -/
theorem ofLocalSections_naturality {n : ℤ} (f : ∀ U : C, GradedLocalHom M L n U)
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U') (i j : ℤ) (hij : i + n = j)
    {U V : Cᵒᵖ} (γ : U ⟶ V) (x : (M.piece i).val.obj U) :
    (L.piece j).val.map γ (ofLocalSections f i j hij U x) =
      ofLocalSections f i j hij V ((M.piece i).val.map γ x) := by
  refine ((f U.unop).naturality i j hij
    (Over.homMk γ.unop (Category.comp_id γ.unop) :
      Over.mk γ.unop ⟶ Over.mk (𝟙 U.unop)) x).trans ?_
  refine ((f U.unop).app_mk_congr i j hij (Category.id_comp γ.unop).symm
    ((M.piece i).val.map γ x)).trans ?_
  exact app_top_congr (hf γ.unop) i j hij _

/-- Assemble a compatible family of local sections of the internal hom, one over each object of
the site, into a homogeneous homomorphism of degree `n`. -/
def ofLocal {n : ℤ} (f : ∀ U : C, GradedLocalHom M L n U)
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U') : GradedHomOfDegree M L n where
  app i j hij :=
    { val :=
        { app := fun U => ModuleCat.ofHom
            { toFun := fun x => ofLocalSections f i j hij U x
              map_add' := fun x y => map_add _ x y
              map_smul' := fun r x =>
                (f U.unop).map_smul i j hij (Over.mk (𝟙 U.unop)) r x }
          naturality := fun {_U _V} γ => ModuleCat.hom_ext (LinearMap.ext fun x =>
            (ofLocalSections_naturality f hf i j hij γ x).symm) } }
  map_mul i j hij p U x b := (f U.unop).map_mul i j hij p (Over.mk (𝟙 U.unop)) x b

/-- The component of `ofLocal f hf` on sections over `U` is the value of `f U` over the
terminal object of the slice site. -/
@[simp]
theorem ofLocal_app {n : ℤ} (f : ∀ U : C, GradedLocalHom M L n U)
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U') (i j : ℤ) (hij : i + n = j)
    (U : Cᵒᵖ) (x : (M.piece i).val.obj U) :
    ((ofLocal f hf).app i j hij).val.app U x =
      (f U.unop).app i j hij (Over.mk (𝟙 U.unop)) x := rfl

/-- Assembling a compatible family of local sections and restricting again returns the
family. -/
theorem toLocal_ofLocal {n : ℤ} (f : ∀ U : C, GradedLocalHom M L n U)
    (hf : ∀ {U U' : C} (g : U' ⟶ U), (f U).restrict g = f U') (U : C) :
    (ofLocal f hf).toLocal U = f U := by
  refine GradedLocalHom.ext fun i j hij V x => ?_
  rw [toLocal_app, ofLocal_app]
  have h := app_top_congr (hf (U := U) (U' := V.left) V.hom) i j hij x
  refine h.symm.trans ?_
  simp only [GradedLocalHom.restrict_app]
  exact (f U).app_mk_congr i j hij (Category.id_comp V.hom) x

/-- A homogeneous homomorphism is determined by its restrictions to the slice sites. -/
theorem eq_of_toLocal {n : ℤ} {φ ψ : GradedHomOfDegree M L n}
    (h : ∀ U : C, φ.toLocal U = ψ.toLocal U) : φ = ψ := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact app_top_congr (h U.unop) i j hij x

end GradedHomOfDegree

/-- A graded sheaf of `R`-modules `G` is the graded internal hom `SheafHom^gr_A(M, L)` of two
right graded `A`-modules when its degree-`n` sections over `U` are the degree-`n` local
homomorphisms `M|_U → L|_U`, additively, `R`-linearly and compatibly with restriction. This is
a characterising property; the internal hom of Stacks 0FR3 is constructed as
`SheafOfModules.gradedSheafHom`, which satisfies it by
`SheafOfModules.isGradedSheafHom_gradedSheafHom`. -/
structure IsGradedSheafHom (M : GradedModule.{t, a, w} A) (L : GradedModule.{t, a, z} A)
    (G : ℤ → SheafOfModules.{h} R) where
  /-- Sections of `G` in degree `n` over `U` are the degree-`n` local homomorphisms
  `M|_U → L|_U`. -/
  sectionsEquiv (n : ℤ) (U : C) : (G n).val.obj (Opposite.op U) ≃ GradedLocalHom M L n U
  /-- The identification is additive. -/
  sectionsEquiv_add (n : ℤ) (U : C) (p q : (G n).val.obj (Opposite.op U)) (i j : ℤ)
      (hij : i + n = j) (V : Over U) (x : (M.piece i).val.obj (Opposite.op V.left)) :
    (sectionsEquiv n U (p + q)).app i j hij V x =
      (sectionsEquiv n U p).app i j hij V x + (sectionsEquiv n U q).app i j hij V x
  /-- The identification is linear over the sheaf of rings. -/
  sectionsEquiv_smul (n : ℤ) (U : C) (r : R.obj.obj (Opposite.op U))
      (p : (G n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left)) :
    (sectionsEquiv n U (r • p)).app i j hij V x =
      R.obj.map V.hom.op r • (sectionsEquiv n U p).app i j hij V x
  /-- The identification is compatible with restriction along a morphism of the site. -/
  sectionsEquiv_naturality (n : ℤ) {U U' : C} (g : U' ⟶ U) (p : (G n).val.obj (Opposite.op U))
      (i j : ℤ) (hij : i + n = j) (V : Over U') :
    (sectionsEquiv n U' ((G n).val.map g.op p)).app i j hij V =
      (sectionsEquiv n U p).app i j hij (Over.mk (V.hom ≫ g))

namespace IsGradedSheafHom

variable {M : GradedModule.{t, a, w} A} {L : GradedModule.{t, a, z} A}
  {G : ℤ → SheafOfModules.{h} R}

/-- A section of the graded internal hom is determined by the local homomorphism it names. -/
theorem sections_ext (hG : IsGradedSheafHom M L G) {n : ℤ} {U : C}
    {p q : (G n).val.obj (Opposite.op U)}
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left)),
      (hG.sectionsEquiv n U p).app i j hij V x = (hG.sectionsEquiv n U q).app i j hij V x) :
    p = q :=
  (hG.sectionsEquiv n U).injective (GradedLocalHom.ext h)

/-- Naming a local homomorphism by a section of the graded internal hom is additive. -/
theorem symm_add (hG : IsGradedSheafHom M L G) (n : ℤ) (U : C)
    (u v w : GradedLocalHom M L n U)
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left)),
      w.app i j hij V x = u.app i j hij V x + v.app i j hij V x) :
    (hG.sectionsEquiv n U).symm w =
      (hG.sectionsEquiv n U).symm u + (hG.sectionsEquiv n U).symm v := by
  refine hG.sections_ext fun i j hij V x => ?_
  rw [hG.sectionsEquiv_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact h i j hij V x

/-- Naming a local homomorphism by a section of the graded internal hom is linear over the
sheaf of rings. -/
theorem symm_smul (hG : IsGradedSheafHom M L G) (n : ℤ) (U : C) (r : R.obj.obj (Opposite.op U))
    (u w : GradedLocalHom M L n U)
    (h : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.piece i).val.obj (Opposite.op V.left)),
      w.app i j hij V x = R.obj.map V.hom.op r • u.app i j hij V x) :
    (hG.sectionsEquiv n U).symm w = r • (hG.sectionsEquiv n U).symm u := by
  refine hG.sections_ext fun i j hij V x => ?_
  rw [hG.sectionsEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h i j hij V x

/-- The degree-`n` sections of the graded internal hom over `U` act on sections over `U`
itself without a scalar restriction. -/
theorem sectionsEquiv_smul_top (hG : IsGradedSheafHom M L G) (n : ℤ) (U : C)
    (r : R.obj.obj (Opposite.op U)) (p : (G n).val.obj (Opposite.op U)) (i j : ℤ)
    (hij : i + n = j) (x : (M.piece i).val.obj (Opposite.op U)) :
    (hG.sectionsEquiv n U (r • p)).app i j hij (Over.mk (𝟙 U)) x =
      r • (hG.sectionsEquiv n U p).app i j hij (Over.mk (𝟙 U)) x := by
  rw [hG.sectionsEquiv_smul, ring_map_top]

/-- Naming a local homomorphism by a section of the graded internal hom is compatible with
restriction along a morphism of the site. -/
theorem symm_naturality (hG : IsGradedSheafHom M L G) (n : ℤ) {U U' : C} (g : U' ⟶ U)
    (u : GradedLocalHom M L n U) :
    (hG.sectionsEquiv n U').symm (u.restrict g) =
      (G n).val.map g.op ((hG.sectionsEquiv n U).symm u) := by
  refine hG.sections_ext fun i j hij V x => ?_
  rw [Equiv.apply_symm_apply, hG.sectionsEquiv_naturality n g, Equiv.apply_symm_apply]
  rfl

end IsGradedSheafHom

/-- A right graded `A`-module `H` is the graded internal hom `SheafHom^gr_B(N, L)` of a graded
`(A, B)`-bimodule `N` and a right graded `B`-module `L` when its underlying graded sheaf of
`R`-modules is that internal hom and its right `A`-action is `(f a)(y) = f (a y)`. This is a
characterising property; the right graded `A`-module of Stacks 0FR4 is constructed as
`SheafOfModules.gradedSheafHomModule`, which satisfies it by
`SheafOfModules.isGradedInternalHom_gradedSheafHomModule`. -/
structure IsGradedInternalHom (N : GradedBimodule.{t, a, z} A B) (L : GradedModule.{t, a, s} B)
    (H : GradedModule.{t, a, h} A) extends IsGradedSheafHom N.toGradedModule L H.piece where
  /-- The right `A`-action on `H` is right multiplication of local homomorphisms. -/
  sectionsEquiv_mul (n m : ℤ) (U : C) (p : (H.piece n).val.obj (Opposite.op U))
      (b : (A.piece m).val.obj (Opposite.op U)) :
    sectionsEquiv (n + m) U (H.smul n m (Opposite.op U) p b) =
      (sectionsEquiv n U p).actRight m b

namespace IsGradedInternalHom

variable {N : GradedBimodule.{t, a, z} A B} {L : GradedModule.{t, a, s} B}
  {H : GradedModule.{t, a, h} A}

/-- The right `A`-action on the graded internal hom, evaluated on sections over the base of the
slice site, where no scalar restriction intervenes. -/
theorem sectionsEquiv_mul_top (hH : IsGradedInternalHom N L H) (n m : ℤ) (U : C)
    (p : (H.piece n).val.obj (Opposite.op U)) (b : (A.piece m).val.obj (Opposite.op U))
    (i j : ℤ) (hij : i + (n + m) = j) (y : (N.piece i).val.obj (Opposite.op U)) :
    (hH.sectionsEquiv (n + m) U (H.smul n m (Opposite.op U) p b)).app i j hij
        (Over.mk (𝟙 U)) y =
      (hH.sectionsEquiv n U p).app (m + i) j (by omega) (Over.mk (𝟙 U))
        ((N.leftMul m i).app (Opposite.op U) b y) := by
  rw [hH.sectionsEquiv_mul, GradedLocalHom.actRight_app, map_top_sections]
  rfl

end IsGradedInternalHom

end SheafOfModules

end
