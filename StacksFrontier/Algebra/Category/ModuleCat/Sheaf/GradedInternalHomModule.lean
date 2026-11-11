module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHomSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModulePullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The internal hom of a graded bimodule, as a right graded module

Let `(C, O)` be a ringed site, let `A` and `B` be sheaves of graded `O`-algebras, let `N` be a
graded `(A, B)`-bimodule and let `L` be a right graded `B`-module. Following [Stacks, Tag 0FR4],
the graded internal hom `SheafHom^gr_B(N, L)` constructed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedInternalHomSheaf.lean` is a right graded
`A`-module, a section `a` of `A^m` acting on a section `f` of `SheafHom^n_B(N, L)` by

`(f a)(y) = f (a y)`,

with no signs. This file constructs that module and the functor, and the functor of graded
categories, `SheafHom^gr_B(N, -)`.

## Main definitions

* `SheafOfModules.GradedHomOfDegree.ofHom`: a homomorphism of right graded modules, read as a
  homogeneous homomorphism of degree `0`; this is how `Mod(A)` sits inside the graded category
  `Mod^gr(A)` of [Stacks, Tag 0FR1].
* `SheafOfModules.gradedSheafHomModule N L`: **the right graded `A`-module
  `SheafHom^gr_B(N, L)`**, whose degree-`n` term is `SheafHom^n_B(N, L)` and whose
  multiplication maps are `SheafOfModules.GradedLocalHom.actRight`.
* `SheafOfModules.gradedSheafHomFunctor N`: the functor
  `SheafHom^gr_B(N, -) : Mod(B) ⥤ Mod(A)`.
* `SheafOfModules.gradedSheafHomMapOfDegree N g`: the image of a homomorphism `g : L → L'`
  homogeneous of degree `k` under `SheafHom^gr_B(N, -)`, homogeneous of degree `k`, and
  `SheafOfModules.gradedSheafHomMapOfDegreeLinear N` the same map as a homomorphism of
  `Γ(C, O)`-modules `Hom^k(L, L') → Hom^k(SheafHom^gr_B(N, L), SheafHom^gr_B(N, L'))`.

## Main results

* `SheafOfModules.isGradedInternalHom_gradedSheafHomModule`: the constructed module *is*
  `SheafHom^gr_B(N, L)` with its right `A`-action, in the sense of
  `SheafOfModules.IsGradedInternalHom`.
* `SheafOfModules.gradedSheafHomMapOfDegree_comp`: `SheafHom^gr_B(N, -)` preserves the
  composition of the graded categories `Mod^gr(B)` and `Mod^gr(A)`, and
  `SheafOfModules.gradedSheafHomMapOfDegree_ofHom` identifies it in degree `0` with
  `SheafOfModules.gradedSheafHomFunctor`, so it also preserves identities. Together with
  `gradedSheafHomMapOfDegreeLinear` this makes `SheafHom^gr_B(N, -)` a functor of graded
  categories `Mod^gr(B) → Mod^gr(A)` over `Γ(C, O)`.

## Implementation notes

The rings of sections of the base are commutative, recorded by the instance argument
`∀ U, IsMulCommutative (R.obj.obj U)`, as for `SheafOfModules.gradedLocalHomSheaf`; this holds for
the structure sheaf of every ringed site. The universes of the site, the sheaf of rings, the
algebras and of `N` and `L` are independent; the internal hom lives in `max u v z s`, the
universe of `SheafOfModules.gradedLocalHomSheaf`.

Postcomposition with a homogeneous homomorphism `g` of degree `k` is defined with an arbitrary
target degree `n'` and a proof of `n + k = n'`, rather than with target degree `n + k`; the
components of a homogeneous homomorphism of the internal homs are then the postcompositions with
no transport.

## References

* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
* [Stacks Project, Tag 0FR3](https://stacks.math.columbia.edu/tag/0FR3)
* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
-/

@[expose] public section

open CategoryTheory Opposite

universe t a w z s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Degree-zero homomorphisms -/

namespace GradedHomOfDegree

variable {A : GradedAlgebra.{t, a} R} {M L : GradedModule.{t, a, w} A}

/-- A homomorphism of right graded modules, read as a homogeneous homomorphism of degree `0`:
its component from degree `i` to degree `j`, where `i + 0 = j`, is the component in degree `i`
followed by the transport to degree `j`. -/
def ofHom (f : M ⟶ L) : GradedHomOfDegree M L 0 where
  app i j hij := f.app i ≫ degCastHom L.piece (by omega)
  map_mul i j hij p U x b := by
    change homSections (degCastHom L.piece (by omega : i + p = j + p)) U
        ((f.app (i + p)).val.app U (M.smul i p U x b)) =
      L.smul j p U (homSections (degCastHom L.piece (by omega : i = j)) U
        ((f.app i).val.app U x)) b
    rw [homSections_degCastHom, homSections_degCastHom, f.map_smul i p U x b,
      Cofree.smul_castHom_left]

/-- The component of `ofHom f` from degree `i` to degree `j` is the component of `f` in degree
`i`, transported to degree `j`. -/
theorem ofHom_app_apply (f : M ⟶ L) (i j : ℤ) (hij : i + 0 = j) (U : Cᵒᵖ)
    (x : (M.piece i).val.obj U) :
    ((ofHom f).app i j hij).val.app U x =
      castHom L.piece (by omega) U ((f.app i).val.app U x) :=
  homSections_degCastHom L.piece _ U _

end GradedHomOfDegree


/-! ### The right action on local homomorphisms -/

namespace GradedLocalHom

variable {A : GradedAlgebra.{t, a} R} {M : GradedModule.{t, a, w} A}
  {L : GradedModule.{t, a, z} A} {U : C}

/-- Two local homomorphisms of propositionally equal degrees with the same values are
heterogeneously equal. -/
theorem heq_of_app {n n' : ℤ} (h : n = n') {f : GradedLocalHom M L n U}
    {g : GradedLocalHom M L n' U}
    (happ : ∀ (i j : ℤ) (hij : i + n = j) (V : Over U)
      (x : (M.piece i).val.obj (op V.left)), f.app i j hij V x = g.app i j (by omega) V x) :
    HEq f g := by
  subst h
  exact heq_of_eq (GradedLocalHom.ext happ)

end GradedLocalHom

/-- The global unit of a sheaf of graded algebras restricts to the global unit. -/
theorem GradedAlgebra.map_one_eval {A : GradedAlgebra.{t, a} R} {U V : Cᵒᵖ} (g : U ⟶ V) :
    (A.piece 0).val.map g (A.one.eval U) = A.one.eval V :=
  PresheafOfModules.sections_property A.one g

namespace GradedLocalHom

variable {A B : GradedAlgebra.{t, a} R} {N : GradedBimodule.{t, a, z} A B}
  {L : GradedModule.{t, a, s} B} {n : ℤ} {U : C}

/-- The right action is additive in the local homomorphism. -/
theorem actRight_add_left (f g : GradedLocalHom N.toGradedModule L n U) (m : ℤ)
    (a : (A.piece m).val.obj (op U)) :
    (f + g).actRight m a = f.actRight m a + g.actRight m a :=
  GradedLocalHom.ext fun _ _ _ _ _ => rfl

/-- The right action is additive in the section of the algebra. -/
theorem actRight_add_right (f : GradedLocalHom N.toGradedModule L n U) (m : ℤ)
    (a a' : (A.piece m).val.obj (op U)) :
    f.actRight m (a + a') = f.actRight m a + f.actRight m a' :=
  GradedLocalHom.ext fun i j hij V y => by
    change f.app (m + i) j _ V ((N.leftMul m i).app (op V.left)
        ((A.piece m).val.map V.hom.op (a + a')) y) =
      f.app (m + i) j _ V ((N.leftMul m i).app (op V.left)
        ((A.piece m).val.map V.hom.op a) y) +
      f.app (m + i) j _ V ((N.leftMul m i).app (op V.left)
        ((A.piece m).val.map V.hom.op a') y)
    exact (congrArg
        (fun c => f.app (m + i) j (by omega) V ((N.leftMul m i).app (op V.left) c y))
        (map_add ((A.piece m).val.map V.hom.op).hom a a')).trans
      ((congrArg (f.app (m + i) j (by omega) V)
          ((N.leftMul m i).map_add_left (op V.left) _ _ y)).trans
        (map_add _ _ _))

/-- The right action is linear over the sheaf of rings in the local homomorphism. -/
theorem actRight_smul_left [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
    (r : R.obj.obj (op U)) (f : GradedLocalHom N.toGradedModule L n U) (m : ℤ)
    (a : (A.piece m).val.obj (op U)) :
    (r • f).actRight m a = r • f.actRight m a :=
  GradedLocalHom.ext fun _ _ _ _ _ => rfl

/-- The right action is linear over the sheaf of rings in the section of the algebra. -/
theorem actRight_smul_right [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
    (r : R.obj.obj (op U)) (f : GradedLocalHom N.toGradedModule L n U) (m : ℤ)
    (a : (A.piece m).val.obj (op U)) :
    f.actRight m (r • a) = r • f.actRight m a :=
  GradedLocalHom.ext fun i j hij V y => by
    change f.app (m + i) j _ V ((N.leftMul m i).app (op V.left)
        ((A.piece m).val.map V.hom.op (r • a)) y) =
      R.obj.map V.hom.op r • f.app (m + i) j _ V ((N.leftMul m i).app (op V.left)
        ((A.piece m).val.map V.hom.op a) y)
    exact (congrArg (fun c => f.app (m + i) j (by omega) V ((N.leftMul m i).app (op V.left) c y))
      (PresheafOfModules.map_smul (A.piece m).val V.hom.op r a)).trans
      ((congrArg (f.app (m + i) j (by omega) V)
        ((N.leftMul m i).map_smul_left (op V.left) _ _ y)).trans
        (f.map_smul (m + i) j (by omega) V _ _))

/-- Restriction commutes with the right action. -/
theorem restrict_actRight {U' : C} (g : U' ⟶ U) (f : GradedLocalHom N.toGradedModule L n U)
    (m : ℤ) (a : (A.piece m).val.obj (op U)) :
    (f.actRight m a).restrict g = (f.restrict g).actRight m ((A.piece m).val.map g.op a) :=
  GradedLocalHom.ext fun i j hij V y => by
    change f.app (m + i) j _ (Over.mk (V.hom ≫ g)) ((N.leftMul m i).app (op V.left)
        ((A.piece m).val.map (V.hom ≫ g).op a) y) =
      f.app (m + i) j _ (Over.mk (V.hom ≫ g)) ((N.leftMul m i).app (op V.left)
        ((A.piece m).val.map V.hom.op ((A.piece m).val.map g.op a)) y)
    rw [op_comp, PresheafOfModules.map_comp_apply]

/-- **The right action is associative**: `(f a) a' = f (a a')`. -/
theorem actRight_actRight (f : GradedLocalHom N.toGradedModule L n U) (i j : ℤ)
    (a : (A.piece i).val.obj (op U)) (a' : (A.piece j).val.obj (op U)) :
    HEq ((f.actRight i a).actRight j a') (f.actRight (i + j) ((A.mul i j).app (op U) a a')) :=
  heq_of_app (add_assoc n i j) fun k l hkl V y => by
    change f.app (i + (j + k)) l _ V ((N.leftMul i (j + k)).app (op V.left)
        ((A.piece i).val.map V.hom.op a) ((N.leftMul j k).app (op V.left)
          ((A.piece j).val.map V.hom.op a') y)) =
      f.app (i + j + k) l _ V ((N.leftMul (i + j) k).app (op V.left)
        ((A.piece (i + j)).val.map V.hom.op ((A.mul i j).app (op U) a a')) y)
    refine f.app_congr_heq _ _ V ?_
    rw [(A.mul i j).naturality V.hom.op a a']
    exact N.left_assoc i j k (op V.left) _ _ y

/-- **The unit acts as the identity**: `f 1 = f`. -/
theorem actRight_one (f : GradedLocalHom N.toGradedModule L n U) :
    HEq (f.actRight 0 (A.one.eval (op U))) f :=
  heq_of_app (add_zero n) fun k l hkl V y => by
    change f.app (0 + k) l _ V ((N.leftMul 0 k).app (op V.left)
        ((A.piece 0).val.map V.hom.op (A.one.eval (op U))) y) = _
    rw [GradedAlgebra.map_one_eval]
    exact f.app_congr_heq _ _ V (N.one_left k (op V.left) y)

end GradedLocalHom

/-! ### The right graded module `SheafHom^gr_B(N, L)` -/

section Module

variable {A B : GradedAlgebra.{t, a} R} [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]

/-- **Stacks 0FR4: `SheafHom^gr_B(N, L)` is a right graded `A`-module.** For a graded
`(A, B)`-bimodule `N` and a right graded `B`-module `L`, the graded `O`-module
`SheafHom^gr_B(N, L)` of [Stacks, Tag 0FR3] with the multiplication maps
`SheafHom^n_B(N, L) × A^m → SheafHom^{n + m}_B(N, L)` sending `(f, a)` to the local
homomorphism `(f a)(y) = f (a y)`, which involves no signs. -/
@[stacks 0FR4 "SheafHom^gr_B(N, L) is a right graded A-module, with (f a)(y) = f(a y)"]
noncomputable def gradedSheafHomModule (N : GradedBimodule.{t, a, z} A B)
    (L : GradedModule.{t, a, s} B) : GradedModule.{t, a, max u v z s} A where
  piece := gradedSheafHom N.toGradedModule L
  smul _ m U := AddMonoidHom.mk'
    (fun f => AddMonoidHom.mk' (fun b => GradedLocalHom.actRight (U := U.unop) f m b)
      (fun b b' => GradedLocalHom.actRight_add_right f m b b'))
    (fun f f' => AddMonoidHom.ext fun b => GradedLocalHom.actRight_add_left f f' m b)
  smul_smul_left _ m U r f b := GradedLocalHom.actRight_smul_left (U := U.unop) r f m b
  smul_smul_right _ m U r f b := GradedLocalHom.actRight_smul_right (U := U.unop) r f m b
  smul_naturality _ m {_ _} g f b := GradedLocalHom.restrict_actRight g.unop f m b
  smul_mul _ i j U f b b' := GradedLocalHom.actRight_actRight (U := U.unop) f i j b b'
  smul_one _ U f := GradedLocalHom.actRight_one (U := U.unop) f

variable (N : GradedBimodule.{t, a, z} A B) (L : GradedModule.{t, a, s} B)

/-- The degree-`n` term of `SheafHom^gr_B(N, L)` is `SheafHom^n_B(N, L)`. -/
@[simp]
theorem gradedSheafHomModule_piece (n : ℤ) :
    (gradedSheafHomModule N L).piece n = gradedLocalHomSheaf N.toGradedModule L n := rfl

/-- The multiplication maps of `SheafHom^gr_B(N, L)` are `(f a)(y) = f (a y)`. -/
theorem gradedSheafHomModule_smul (n m : ℤ) (U : C)
    (f : GradedLocalHom N.toGradedModule L n U) (b : (A.piece m).val.obj (op U)) :
    (gradedSheafHomModule N L).smul n m (op U) f b = f.actRight m b := rfl

/-- **The constructed module is the internal hom with its right `A`-action**, in the sense of
`SheafOfModules.IsGradedInternalHom`. -/
@[stacks 0FR4 "the right graded A-module SheafHom^gr_B(N, L), as the internal hom with its
right A-action"]
noncomputable def isGradedInternalHom_gradedSheafHomModule :
    IsGradedInternalHom N L (gradedSheafHomModule N L) where
  toIsGradedSheafHom := isGradedSheafHom_gradedSheafHom N.toGradedModule L
  sectionsEquiv_mul _ _ _ _ _ := rfl

end Module


/-! ### Postcomposition -/

namespace GradedLocalHom

variable {A : GradedAlgebra.{t, a} R} {M : GradedModule.{t, a, w} A}
  {L L' : GradedModule.{t, a, s} A} {n k : ℤ} {U : C}

/-- Postcomposition of a local homomorphism with a homomorphism of right graded modules. -/
def postcompHom (φ : L ⟶ L') (f : GradedLocalHom M L n U) : GradedLocalHom M L' n U where
  app i j hij V := (homSections (φ.app j) (op V.left)).comp (f.app i j hij V)
  map_smul i j hij V r x :=
    (congrArg (homSections (φ.app j) (op V.left)) (f.map_smul i j hij V r x)).trans
      (homSections_smul _ _ _ _)
  naturality i j hij {_V _W} q x :=
    (homSections_naturality (φ.app j) q.left.op _).trans
      (congrArg (homSections (φ.app j) _) (f.naturality i j hij q x))
  map_mul i j hij p V x b :=
    (congrArg (homSections (φ.app (j + p)) (op V.left)) (f.map_mul i j hij p V x b)).trans
      (φ.map_smul j p _ _ b)

/-- The value of `f.postcompHom φ` is `φ` applied to the value of `f`. -/
@[simp]
theorem postcompHom_app (φ : L ⟶ L') (f : GradedLocalHom M L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (M.piece i).val.obj (op V.left)) :
    (f.postcompHom φ).app i j hij V x = (φ.app j).val.app (op V.left) (f.app i j hij V x) := rfl

/-- Composing a local homomorphism with a homogeneous homomorphism through two propositionally
equal intermediate degrees gives the same value. -/
theorem homOfDegree_app_app_congr (g : GradedHomOfDegree L L' k) (f : GradedLocalHom M L n U)
    {i l l' j : ℤ} (hl : i + n = l) (hl' : i + n = l') (hlj : l + k = j) (hlj' : l' + k = j)
    (V : Over U) (x : (M.piece i).val.obj (op V.left)) :
    (g.app l j hlj).val.app (op V.left) (f.app i l hl V x) =
      (g.app l' j hlj').val.app (op V.left) (f.app i l' hl' V x) := by
  subst hl hl'
  rfl

/-- Postcomposition of a local homomorphism of degree `n` with a homogeneous homomorphism of
degree `k`, a local homomorphism of degree `n'` for `n + k = n'`. -/
def postcomp (g : GradedHomOfDegree L L' k) (f : GradedLocalHom M L n U) {n' : ℤ}
    (h : n + k = n') : GradedLocalHom M L' n' U where
  app i j hij V :=
    (homSections (g.app (i + n) j (by omega)) (op V.left)).comp (f.app i (i + n) rfl V)
  map_smul i j hij V r x :=
    (congrArg (homSections (g.app (i + n) j (by omega)) (op V.left))
      (f.map_smul i (i + n) rfl V r x)).trans (homSections_smul _ _ _ _)
  naturality i j hij {_V _W} q x :=
    (homSections_naturality (g.app (i + n) j (by omega)) q.left.op _).trans
      (congrArg (homSections (g.app (i + n) j (by omega)) _) (f.naturality i (i + n) rfl q x))
  map_mul i j hij p V x b :=
    (homOfDegree_app_app_congr g f rfl (show i + p + n = i + n + p by omega) (by omega)
        (by omega) V _).trans
      ((congrArg (homSections (g.app (i + n + p) (j + p) (by omega)) (op V.left))
          (f.map_mul i (i + n) rfl p V x b)).trans
        (g.map_mul (i + n) j (by omega) p (op V.left) _ b))

/-- The value of `f.postcomp g h` is `g` applied to the value of `f`. -/
theorem postcomp_app (g : GradedHomOfDegree L L' k) (f : GradedLocalHom M L n U) {n' : ℤ}
    (h : n + k = n') (i j : ℤ) (hij : i + n' = j) (l : ℤ) (hl : i + n = l) (V : Over U)
    (x : (M.piece i).val.obj (op V.left)) :
    (f.postcomp g h).app i j hij V x =
      (g.app l j (by omega)).val.app (op V.left) (f.app i l hl V x) := by
  subst hl
  rfl

end GradedLocalHom

/-! ### The functor `SheafHom^gr_B(N, -)` -/

section Functor

variable {A B : GradedAlgebra.{t, a} R} [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
  (N : GradedBimodule.{t, a, z} A B) {L L' L'' : GradedModule.{t, a, s} B}

/-- Postcomposition with a homomorphism of right graded `B`-modules, as a morphism
`SheafHom^n_B(N, L) ⟶ SheafHom^n_B(N, L')` of sheaves of modules. -/
noncomputable def gradedSheafHomPostcompHom (φ : L ⟶ L') (n : ℤ) :
    gradedLocalHomSheaf N.toGradedModule L n ⟶ gradedLocalHomSheaf N.toGradedModule L' n where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun f => GradedLocalHom.postcompHom (U := U.unop) φ f
          map_add' := fun _ _ => GradedLocalHom.ext fun _ _ _ _ _ =>
            AddMonoidHom.map_add (homSections _ _) _ _
          map_smul' := fun _ _ => GradedLocalHom.ext fun _ _ _ _ _ => homSections_smul _ _ _ _ }
      naturality := fun {_U _V} _q => ModuleCat.hom_ext (LinearMap.ext fun _f => rfl) }

/-- On a local section `f`, `gradedSheafHomPostcompHom N φ n` is postcomposition with `φ`. -/
theorem gradedSheafHomPostcompHom_apply (φ : L ⟶ L') (n : ℤ) (U : C)
    (f : GradedLocalHom N.toGradedModule L n U) :
    (gradedSheafHomPostcompHom N φ n).val.app (op U) f = f.postcompHom φ := rfl

/-- **Stacks 0FR4, functoriality.** The homomorphism
`SheafHom^gr_B(N, L) ⟶ SheafHom^gr_B(N, L')` of right graded `A`-modules induced by a
homomorphism `φ : L ⟶ L'` of right graded `B`-modules: postcomposition with `φ`. -/
noncomputable def gradedSheafHomMap (φ : L ⟶ L') :
    gradedSheafHomModule N L ⟶ gradedSheafHomModule N L' where
  app n := gradedSheafHomPostcompHom N φ n
  map_smul _ _ _ _ _ := GradedLocalHom.ext fun _ _ _ _ _ => rfl

/-- Degree `n` of `gradedSheafHomMap N φ` is postcomposition with `φ`. -/
theorem gradedSheafHomMap_app (φ : L ⟶ L') (n : ℤ) :
    (gradedSheafHomMap N φ).app n = gradedSheafHomPostcompHom N φ n := rfl

/-- **Stacks 0FR4: the functor `SheafHom^gr_B(N, -) : Mod(B) ⥤ Mod(A)`**, from right graded
`B`-modules to right graded `A`-modules, sending `L` to `SheafHom^gr_B(N, L)` and a homomorphism
to postcomposition with it. -/
@[stacks 0FR4 "the functor SheafHom^gr_B(N, -) : Mod(B) → Mod(A)"]
noncomputable def gradedSheafHomFunctor (N : GradedBimodule.{t, a, z} A B) :
    GradedModule.{t, a, s} B ⥤ GradedModule.{t, a, max u v z s} A where
  obj L := gradedSheafHomModule N L
  map φ := gradedSheafHomMap N φ
  map_id _ := GradedModule.Hom.ext fun _ => SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))
  map_comp _ _ := GradedModule.Hom.ext fun _ => SheafOfModules.hom_ext
    (PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- The functor `SheafHom^gr_B(N, -)` sends `L` to `SheafHom^gr_B(N, L)`. -/
@[simp]
theorem gradedSheafHomFunctor_obj (L : GradedModule.{t, a, s} B) :
    (gradedSheafHomFunctor N).obj L = gradedSheafHomModule N L := rfl

/-- The functor `SheafHom^gr_B(N, -)` sends `φ` to postcomposition with `φ`. -/
@[simp]
theorem gradedSheafHomFunctor_map (φ : L ⟶ L') :
    (gradedSheafHomFunctor N).map φ = gradedSheafHomMap N φ := rfl

variable {k k' : ℤ}

/-- Postcomposition with a homogeneous homomorphism `g : L → L'` of degree `k`, as a morphism
`SheafHom^n_B(N, L) ⟶ SheafHom^{n'}_B(N, L')` of sheaves of modules, for `n + k = n'`. -/
noncomputable def gradedSheafHomPostcomp (g : GradedHomOfDegree L L' k) (n n' : ℤ)
    (h : n + k = n') :
    gradedLocalHomSheaf N.toGradedModule L n ⟶ gradedLocalHomSheaf N.toGradedModule L' n' where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun f => GradedLocalHom.postcomp (U := U.unop) g f h
          map_add' := fun _ _ => GradedLocalHom.ext fun _ _ _ _ _ =>
            AddMonoidHom.map_add (homSections _ _) _ _
          map_smul' := fun _ _ => GradedLocalHom.ext fun _ _ _ _ _ => homSections_smul _ _ _ _ }
      naturality := fun {_U _V} _q => ModuleCat.hom_ext (LinearMap.ext fun _f => rfl) }

/-- On a local section `f`, `gradedSheafHomPostcomp N g n n' h` is postcomposition with `g`. -/
theorem gradedSheafHomPostcomp_apply (g : GradedHomOfDegree L L' k) (n n' : ℤ) (h : n + k = n')
    (U : C) (f : GradedLocalHom N.toGradedModule L n U) :
    (gradedSheafHomPostcomp N g n n' h).val.app (op U) f = f.postcomp g h := rfl

/-- **Stacks 0FR4, the functor of graded categories `SheafHom^gr_B(N, -)`, on morphisms.** A
homomorphism `g : L → L'` of right graded `B`-modules homogeneous of degree `k` induces the
homomorphism `SheafHom^gr_B(N, L) → SheafHom^gr_B(N, L')` of right graded `A`-modules
homogeneous of degree `k` given by postcomposition with `g`. -/
@[stacks 0FR4 "SheafHom^gr_B(N, -) : Mod^gr(B) → Mod^gr(A) on homogeneous homomorphisms of
degree k"]
noncomputable def gradedSheafHomMapOfDegree (g : GradedHomOfDegree L L' k) :
    GradedHomOfDegree (gradedSheafHomModule N L) (gradedSheafHomModule N L') k where
  app i j hij := gradedSheafHomPostcomp N g i j hij
  map_mul i j hij p U f b := GradedLocalHom.ext fun q r hqr V y =>
    GradedLocalHom.homOfDegree_app_app_congr g f (i := p + q) (by omega) rfl (by omega)
      (by omega) V _

/-- The components of `gradedSheafHomMapOfDegree N g` are the postcompositions with `g`. -/
theorem gradedSheafHomMapOfDegree_app (g : GradedHomOfDegree L L' k) (i j : ℤ)
    (hij : i + k = j) :
    (gradedSheafHomMapOfDegree N g).app i j hij = gradedSheafHomPostcomp N g i j hij := rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- Two composites of homogeneous homomorphisms through propositionally equal intermediate
degrees agree on sections. -/
private theorem homOfDegree_app_app_congr' {K : GradedModule.{t, a, s} B}
    (g : GradedHomOfDegree K L k) (g' : GradedHomOfDegree L L' k') {i l l' j : ℤ}
    (hl : i + k = l) (hl' : i + k = l') (hlj : l + k' = j) (hlj' : l' + k' = j) (U : Cᵒᵖ)
    (x : (K.piece i).val.obj U) :
    (g'.app l j hlj).val.app U ((g.app i l hl).val.app U x) =
      (g'.app l' j hlj').val.app U ((g.app i l' hl').val.app U x) := by
  subst hl hl'
  rfl

/-- **`SheafHom^gr_B(N, -)` preserves composition in the graded categories**:
`(g' ∘ g)_* = g'_* ∘ g_*`. -/
theorem gradedSheafHomMapOfDegree_comp (g : GradedHomOfDegree L L' k)
    (g' : GradedHomOfDegree L' L'' k') :
    gradedSheafHomMapOfDegree N (g'.comp g) =
      (gradedSheafHomMapOfDegree N g').comp (gradedSheafHomMapOfDegree N g) := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  rw [GradedHomOfDegree.comp_app]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun f => GradedLocalHom.ext fun q r hqr V y => ?_))
  change ((g'.comp g).app (q + i) r (by omega)).val.app (op V.left) (f.app q (q + i) rfl V y) =
    (g'.app (q + (i + k)) r (by omega)).val.app (op V.left)
      ((g.app (q + i) (q + (i + k)) (by omega)).val.app (op V.left) (f.app q (q + i) rfl V y))
  rw [GradedHomOfDegree.comp_app]
  exact homOfDegree_app_app_congr' g g' rfl (by omega) _ _ _ _

/-- `SheafHom^gr_B(N, -)` is additive on homogeneous homomorphisms of degree `k`. -/
theorem gradedSheafHomMapOfDegree_add (g g' : GradedHomOfDegree L L' k) :
    gradedSheafHomMapOfDegree N (g + g') =
      gradedSheafHomMapOfDegree N g + gradedSheafHomMapOfDegree N g' := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  rw [GradedHomOfDegree.add_app]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun f => GradedLocalHom.ext fun q r hqr V y => ?_))
  change ((g + g').app (q + i) r (by omega)).val.app (op V.left) (f.app q (q + i) rfl V y) =
    (g.app (q + i) r (by omega)).val.app (op V.left) (f.app q (q + i) rfl V y) +
      (g'.app (q + i) r (by omega)).val.app (op V.left) (f.app q (q + i) rfl V y)
  rw [GradedHomOfDegree.add_app]
  rfl

/-- `SheafHom^gr_B(N, -)` is linear over the global sections `Γ(C, O)` on homogeneous
homomorphisms of degree `k`. -/
theorem gradedSheafHomMapOfDegree_smul (c : Stacks.Cohomology.SiteModules.GlobalSectionRing R)
    (g : GradedHomOfDegree L L' k) :
    gradedSheafHomMapOfDegree N (c • g) = c • gradedSheafHomMapOfDegree N g := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun f => GradedLocalHom.ext fun q r hqr V y => ?_))
  rw [GradedHomOfDegree.smul_app_apply]
  change ((c • g).app (q + i) r (by omega)).val.app (op V.left) (f.app q (q + i) rfl V y) =
    R.obj.map V.hom.op (c.1 U) •
      (g.app (q + i) r (by omega)).val.app (op V.left) (f.app q (q + i) rfl V y)
  rw [GradedHomOfDegree.smul_app_apply, ← c.2 V.hom.op]
  rfl

/-- **Stacks 0FR4: `SheafHom^gr_B(N, -)` is a functor of graded categories over `Γ(C, O)`, on
the morphisms of degree `k`**: the map
`Hom^k(L, L') → Hom^k(SheafHom^gr_B(N, L), SheafHom^gr_B(N, L'))` is `Γ(C, O)`-linear. Its
compatibility with composition is `SheafOfModules.gradedSheafHomMapOfDegree_comp`, and with
identities `SheafOfModules.gradedSheafHomMapOfDegree_ofHom`. -/
@[stacks 0FR4 "SheafHom^gr_B(N, -) is Γ(C, O)-linear on Hom^k, as a functor of graded
categories"]
noncomputable def gradedSheafHomMapOfDegreeLinear (L L' : GradedModule.{t, a, s} B) (k : ℤ) :
    GradedHomOfDegree L L' k →ₗ[Stacks.Cohomology.SiteModules.GlobalSectionRing R]
      GradedHomOfDegree (gradedSheafHomModule N L) (gradedSheafHomModule N L') k where
  toFun := gradedSheafHomMapOfDegree N
  map_add' := gradedSheafHomMapOfDegree_add N
  map_smul' := gradedSheafHomMapOfDegree_smul N

/-- **In degree `0`, `SheafHom^gr_B(N, -)` on the graded categories is the functor
`SheafHom^gr_B(N, -) : Mod(B) ⥤ Mod(A)`.** In particular it sends identities to identities. -/
theorem gradedSheafHomMapOfDegree_ofHom (φ : L ⟶ L') :
    gradedSheafHomMapOfDegree N (GradedHomOfDegree.ofHom φ) =
      GradedHomOfDegree.ofHom (gradedSheafHomMap N φ) := by
  refine GradedHomOfDegree.ext fun i j hij => ?_
  obtain rfl : j = i := by omega
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun f => GradedLocalHom.ext fun q r hqr V y => ?_))
  change ((GradedHomOfDegree.ofHom φ).app (q + j) r (by omega)).val.app (op V.left)
      (f.app q (q + j) rfl V y) =
    (((GradedHomOfDegree.ofHom (gradedSheafHomMap N φ)).app j j hij).val.app U f).app q r hqr V y
  rw [GradedHomOfDegree.ofHom_app_apply, GradedHomOfDegree.ofHom_app_apply]
  subst hqr
  rfl

end Functor

end SheafOfModules
