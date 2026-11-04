module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInternalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The differential graded endomorphism algebra and bimodule structures

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` and `B` be sheaves of differential graded
`R`-algebras and let `N` be a right differential graded `B`-module. The internal hom
`SheafHom^dg_B(N, N)` of Tag 0FRN is then a sheaf of differential graded `R`-algebras, with
composition of local endomorphisms as multiplication and the identity as unit, and the
`(A, B)`-bimodule structures on `N` extending the given right `B`-action are in bijection with
the identity-preserving homomorphisms of sheaves of differential graded algebras

`A ⟶ SheafHom^dg_B(N, N)`.

## Main definitions

* `SheafOfModules.IsEndomorphismAlgebra` says that a sheaf of differential graded `R`-algebras
  `E` *is* the endomorphism algebra `SheafHom^dg_B(N, N)`: its underlying complex is an internal
  hom of `N` with itself, its multiplication is composition of local endomorphisms and its unit
  is the identity.
* `SheafOfModules.endomorphismAlgebraOfIsInternalHom` is the sheaf of differential graded
  algebras carried by a complex which is an internal hom of `N` with itself; its multiplication
  is `SheafOfModules.internalHomMul` and its unit is `SheafOfModules.internalHomOne`.
* `SheafOfModules.UnitalHom` is a homomorphism of sheaves of differential graded algebras which
  preserves the identity on every object of the site.
* `SheafOfModules.BimoduleStructure` is an `(A, B)`-bimodule structure on `N` compatible with
  its given right `B`-action, and `SheafOfModules.BimoduleStructure.toBimodule` exhibits such a
  structure as a differential graded bimodule in the sense of Tag 0FRQ.
* `SheafOfModules.bimoduleStructureEquiv` is the bijection between compatible bimodule
  structures on `N` and identity-preserving homomorphisms `A ⟶ SheafHom^dg_B(N, N)`. Its two
  directions are `SheafOfModules.actionHom`, which sends a bimodule structure to the
  homomorphism acting by left multiplication, and `SheafOfModules.homBimoduleStructure`, which
  sends a homomorphism to the left action by the local endomorphisms it names.

## Main results

* `SheafOfModules.isEndomorphismAlgebra_endomorphismAlgebraOfIsInternalHom`: the algebra built
  on an internal hom of `N` with itself is an endomorphism algebra of `N`.
* `SheafOfModules.BimoduleStructure.toBimodule_complex` and
  `SheafOfModules.BimoduleStructure.toBimodule_leftMul`: the bimodule built from a compatible
  structure has the complex and the left action it was built from.
* `SheafOfModules.bimoduleStructureEquiv_app` pins the bijection down: the homomorphism attached
  to a bimodule structure acts on local sections of `N` by left multiplication for that
  structure.

## Implementation notes

The internal hom is not constructed here; it is used through the predicate
`SheafOfModules.IsInternalHom` of Tag 0FRN, which pins a complex of sheaves of `R`-modules by
its local sections. Consequently the algebra structure is produced *conditionally*, from a
complex `H` together with a proof that `H` is an internal hom of `N` with itself, and the
correspondence is stated for an arbitrary sheaf of differential graded algebras `E` satisfying
`IsEndomorphismAlgebra N E`. This is more general than fixing a choice, and determines the
object up to canonical isomorphism.

`SheafOfModules.DifferentialGradedAlgebra.Hom` preserves multiplication but does not require
preservation of the identity, matching the source for Tag 0FRF. The source for the present tag
explicitly requires identity-preserving maps, so the correspondence uses
`SheafOfModules.UnitalHom`, which adds precisely that condition.

A "bimodule structure on `N` compatible with the given differential graded `B`-module structure"
is rendered literally, as an extra left `A`-action on the complex of `N` rather than as a
separate bimodule object together with an identification. This is what keeps both sides of the
correspondence free of transport along an equality of complexes;
`SheafOfModules.BimoduleStructure.toBimodule` then shows that such a structure is exactly a
differential graded bimodule whose underlying right `B`-module is `N`.

Degrees are carried in the form `(i, j, hij : i + n = j)` of Tag 0FRN wherever local sections of
the internal hom are involved, so that the two sides of each formula are sections of one and the
same sheaf. The laws of the algebra and of the bimodule, on the other hand, are those of Tags
0FRF and 0FRQ, whose degrees are propositionally but not definitionally equal; those are stated
with `HEq` and `SheafOfModules.gradedCast`, as in the source files for those tags.

The auxiliary constructions and lemmas are recorded publicly rather than kept private, because
the two main definitions are sheaves of differential graded algebras and an `Equiv`, whose
values are only usable through the lemmas describing them.

The restriction maps of a presheaf of modules land in a restriction of scalars, so a section of
`M` over `V` restricted from `U` has the type `(ModuleCat.restrictScalars _).obj (M.obj V)`
rather than `M.obj V` on the nose. The two are definitionally equal, but the equality is not
visible at the transparency at which a tactic checks that its goal is type-correct, so a
rewriting step in a goal mentioning a restricted section fails. The restricted section is
therefore written `SheafOfModules.restrictSection`, which records the type of the value on the
nose, in every statement a proof below has to rewrite in; `SheafOfModules.restrictSection_id`,
`_comp`, `_add`, `_smul`, `_val_app` and `_bilinearMap` are the rules it is manipulated by.

The universes of the site, of the sheaf of rings, of the algebras `A` and `B`, of the module `N`
and of the complex underlying the endomorphism algebra are independent, except that `A` and the
endomorphism algebra must have the same module universe to be objects of one category of sheaves
of differential graded algebras; this is forced by the statement of the correspondence, not by
the construction.

## References

* [Stacks Project, Tag 0FRR](https://stacks.math.columbia.edu/tag/0FRR)
* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public section

open CategoryTheory

universe t a w s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R}

/-- Restriction of a local section of a sheaf of modules along a morphism of the site. This is
`M.val.map f x`; naming it records the type of the value as `M.val.obj V` on the nose, where
`M.val.map f x` presents it as a section of a restriction of scalars. -/
noncomputable def restrictSection (M : SheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) : M.val.obj V :=
  show M.val.obj V from M.val.map f x

/-- Restricting a section along an identity does nothing. -/
@[simp]
theorem restrictSection_id (M : SheafOfModules.{w} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    restrictSection M (𝟙 U) x = x :=
  congrArg (fun g => g x) ((M.val.presheaf ⋙ CategoryTheory.forget Ab).map_id U)

/-- Restriction of sections is functorial. -/
theorem restrictSection_comp (M : SheafOfModules.{w} R) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (x : M.val.obj U) :
    restrictSection M (f ≫ g) x = restrictSection M g (restrictSection M f x) :=
  PresheafOfModules.map_comp_apply M.val f g x

/-- Restriction of sections is additive. -/
theorem restrictSection_add (M : SheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x y : M.val.obj U) :
    restrictSection M f (x + y) = restrictSection M f x + restrictSection M f y :=
  map_add (M.val.map f).hom x y

/-- Restriction of sections is semilinear over the sheaf of rings. -/
theorem restrictSection_smul (M : SheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : R.obj.obj U) (x : M.val.obj U) :
    restrictSection M f (r • x) = R.obj.map f r • restrictSection M f x :=
  M.val.map_smul f r x

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem restrictSection_val_app {M P : SheafOfModules.{w} R} (φ : M ⟶ P) {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : M.val.obj U) :
    restrictSection P f (φ.val.app U x) = φ.val.app V (restrictSection M f x) :=
  (PresheafOfModules.naturality_apply φ.val f x).symm

/-- A bilinear map of sheaves of modules commutes with restriction of sections. -/
theorem restrictSection_bilinearMap {M : SheafOfModules.{a} R} {P : SheafOfModules.{w} R}
    {Q : SheafOfModules.{s} R} (β : BilinearMap M P Q) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) (y : P.val.obj U) :
    restrictSection Q f (β.app U x y) =
      β.app V (restrictSection M f x) (restrictSection P f y) :=
  β.naturality f x y

/-- A sheaf of differential graded `R`-algebras `E` is the differential graded endomorphism
algebra `SheafHom^dg_B(N, N)` of a right differential graded `B`-module `N` when its underlying
complex is an internal hom of `N` with itself, its multiplication is composition of local
endomorphisms and its unit is the identity. -/
structure IsEndomorphismAlgebra (N : DifferentialGradedModule.{t, a, w} B)
    (E : DifferentialGradedAlgebra.{t, s} R) where
  /-- The underlying complex of `E` is the internal hom `SheafHom^dg_B(N, N)`. -/
  isInternalHom : IsInternalHom N N E.complex
  /-- Multiplication in `E` is composition of local endomorphisms. -/
  mul_spec (n m : ℤ) (U : C) (a : (E.complex.X n).val.obj (Opposite.op U))
      (b : (E.complex.X m).val.obj (Opposite.op U)) :
    isInternalHom.sectionsEquiv (n + m) U ((E.mul n m).app (Opposite.op U) a b) =
      LocalHom.comp (isInternalHom.sectionsEquiv m U b) (isInternalHom.sectionsEquiv n U a)
        (add_comm m n)
  /-- The unit of `E` is the identity local endomorphism. -/
  one_spec (U : C) (i j : ℤ) (hij : i + 0 = j) (V : Over U)
      (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    HEq ((isInternalHom.sectionsEquiv 0 U (E.one.eval (Opposite.op U))).app i j hij V x) x

/-! ### The algebra structure on an internal hom

Composition of local endomorphisms and the identity make a complex which is an internal hom of
`N` with itself into a sheaf of differential graded algebras. -/

section EndomorphismAlgebra

variable {N : DifferentialGradedModule.{t, a, w} B}
  {H : CochainComplex (SheafOfModules.{s} R) ℤ}

/-- Transporting a section along an equality of degrees does not change it, up to `HEq`. -/
theorem heq_of_gradedCast_eq {F : ℤ → Type*} {i j : ℤ} (h : i = j) (x : F i) (y : F j)
    (hxy : gradedCast F h x = y) : HEq x y := by
  cases h
  exact heq_of_eq hxy

/-- The identity local homomorphism acts as the identity on local sections. -/
theorem localHom_id_app {M : DifferentialGradedModule.{t, a, w} A} {U : C} {i j : ℤ}
    (hij : i + 0 = j) (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    HEq ((LocalHom.id M U).app i j hij V x) x := by
  obtain rfl : i = j := by omega
  exact HEq.rfl

/-- The identity local homomorphism acts as the identity, in the degree-preserving form. -/
theorem localHom_id_app_self {M : DifferentialGradedModule.{t, a, w} A} {U : C} {i : ℤ}
    (hij : i + 0 = i) (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (LocalHom.id M U).app i i hij V x = x := rfl

/-- The composition of the local endomorphisms named by two sections of an internal hom, computed
through an arbitrary intermediate degree. -/
theorem localHom_comp_sections_app (hH : IsInternalHom N N H) {n m : ℤ} {U : C}
    (a : (H.X n).val.obj (Opposite.op U)) (b : (H.X m).val.obj (Opposite.op U))
    {i j : ℤ} (hij : i + (n + m) = j) (i' : ℤ) (hii' : i + m = i') (hj : i' + n = j)
    (V : Over U) (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (LocalHom.comp (hH.sectionsEquiv m U b) (hH.sectionsEquiv n U a) (add_comm m n)).app i j hij
        V x =
      (hH.sectionsEquiv n U a).app i' j hj V ((hH.sectionsEquiv m U b).app i i' hii' V x) :=
  LocalHom.comp_app _ _ _ hii' hj V x

/-- The unit of the endomorphism algebra: the global section of the degree-zero part of an
internal hom of `N` with itself which is the identity over every object of the site. -/
noncomputable def internalHomOne (hH : IsInternalHom N N H) : (H.X 0).sections :=
  (H.X 0).val.sectionsMk (fun U => (hH.sectionsEquiv 0 U.unop).symm (LocalHom.id N U.unop))
    (fun {U V} f => by
      apply (hH.sectionsEquiv 0 V.unop).injective
      refine LocalHom.ext fun i j hij W x => ?_
      have h := hH.sectionsEquiv_naturality 0 f.unop
        ((hH.sectionsEquiv 0 U.unop).symm (LocalHom.id N U.unop)) i j hij W
      rw [Quiver.Hom.op_unop] at h
      rw [DFunLike.congr_fun h x, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      obtain rfl : i = j := by omega
      rfl)

/-- The unit of the endomorphism algebra names the identity local endomorphism. -/
theorem internalHomOne_eval (hH : IsInternalHom N N H) (U : C) :
    hH.sectionsEquiv 0 U ((internalHomOne hH).eval (Opposite.op U)) = LocalHom.id N U :=
  Equiv.apply_symm_apply _ _

/-- The unit of the endomorphism algebra acts as the identity on local sections of `N`. -/
theorem internalHomOne_app (hH : IsInternalHom N N H) (U : C) {i j : ℤ} (hij : i + 0 = j)
    (V : Over U) (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    HEq ((hH.sectionsEquiv 0 U ((internalHomOne hH).eval (Opposite.op U))).app i j hij V x) x := by
  rw [internalHomOne_eval]
  exact localHom_id_app hij V x

/-- Composition of local endomorphisms, as a biadditive map on the sections of an internal hom of
`N` with itself over a fixed object of the site. -/
noncomputable def internalHomMulRight (hH : IsInternalHom N N H) (n m : ℤ) (U : Cᵒᵖ)
    (a : (H.X n).val.obj U) : (H.X m).val.obj U →+ (H.X (n + m)).val.obj U where
  toFun b := (hH.sectionsEquiv (n + m) U.unop).symm
    (LocalHom.comp (hH.sectionsEquiv m U.unop b) (hH.sectionsEquiv n U.unop a) (add_comm m n))
  map_zero' := by
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [Equiv.apply_symm_apply,
      localHom_comp_sections_app hH a 0 hij (i + m) rfl (by omega) V x,
      hH.sectionsEquiv_zero, map_zero, hH.sectionsEquiv_zero]
  map_add' b b' := by
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [Equiv.apply_symm_apply, hH.sectionsEquiv_add, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply,
      localHom_comp_sections_app hH a (b + b') hij (i + m) rfl (by omega) V x,
      localHom_comp_sections_app hH a b hij (i + m) rfl (by omega) V x,
      localHom_comp_sections_app hH a b' hij (i + m) rfl (by omega) V x,
      hH.sectionsEquiv_add, map_add]

/-- The product of two sections of an internal hom names the composition of the local
endomorphisms they name. -/
theorem internalHomMulRight_sectionsEquiv (hH : IsInternalHom N N H) (n m : ℤ) (U : Cᵒᵖ)
    (a : (H.X n).val.obj U) (b : (H.X m).val.obj U) :
    hH.sectionsEquiv (n + m) U.unop (internalHomMulRight hH n m U a b) =
      LocalHom.comp (hH.sectionsEquiv m U.unop b) (hH.sectionsEquiv n U.unop a) (add_comm m n) :=
  Equiv.apply_symm_apply _ _

/-- Composition of local endomorphisms, as a biadditive map on the sections of an internal hom
of `N` with itself over a fixed object of the site. -/
noncomputable def internalHomMulApp (hH : IsInternalHom N N H) (n m : ℤ) (U : Cᵒᵖ) :
    (H.X n).val.obj U →+ (H.X m).val.obj U →+ (H.X (n + m)).val.obj U where
  toFun a := internalHomMulRight hH n m U a
  map_zero' := by
    refine AddMonoidHom.ext fun b => ?_
    change internalHomMulRight hH n m U 0 b = 0
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [internalHomMulRight_sectionsEquiv,
      localHom_comp_sections_app hH 0 b hij (i + m) rfl (by omega) V x,
      hH.sectionsEquiv_zero, hH.sectionsEquiv_zero]
  map_add' a a' := by
    refine AddMonoidHom.ext fun b => ?_
    change internalHomMulRight hH n m U (a + a') b =
      internalHomMulRight hH n m U a b + internalHomMulRight hH n m U a' b
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [internalHomMulRight_sectionsEquiv, hH.sectionsEquiv_add,
      internalHomMulRight_sectionsEquiv, internalHomMulRight_sectionsEquiv,
      localHom_comp_sections_app hH (a + a') b hij (i + m) rfl (by omega) V x,
      localHom_comp_sections_app hH a b hij (i + m) rfl (by omega) V x,
      localHom_comp_sections_app hH a' b hij (i + m) rfl (by omega) V x,
      hH.sectionsEquiv_add]

/-- The product of two sections of an internal hom names the composition of the local
endomorphisms they name. -/
theorem internalHomMulApp_sectionsEquiv (hH : IsInternalHom N N H) (n m : ℤ) (U : Cᵒᵖ)
    (a : (H.X n).val.obj U) (b : (H.X m).val.obj U) :
    hH.sectionsEquiv (n + m) U.unop (internalHomMulApp hH n m U a b) =
      LocalHom.comp (hH.sectionsEquiv m U.unop b) (hH.sectionsEquiv n U.unop a) (add_comm m n) :=
  Equiv.apply_symm_apply _ _

/-- The product of two sections of an internal hom, on local sections of `N`. -/
theorem internalHomMulApp_app (hH : IsInternalHom N N H) (n m : ℤ) (U : Cᵒᵖ)
    (a : (H.X n).val.obj U) (b : (H.X m).val.obj U) {i j : ℤ} (hij : i + (n + m) = j)
    (V : Over U.unop) (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (hH.sectionsEquiv (n + m) U.unop (internalHomMulApp hH n m U a b)).app i j hij V x =
      (hH.sectionsEquiv n U.unop a).app (i + m) j (by omega) V
        ((hH.sectionsEquiv m U.unop b).app i (i + m) rfl V x) := by
  rw [internalHomMulApp_sectionsEquiv]
  exact localHom_comp_sections_app hH a b hij (i + m) rfl (by omega) V x

/-- Composition of local endomorphisms, as the multiplication of the endomorphism algebra. -/
noncomputable def internalHomMul (hH : IsInternalHom N N H) (n m : ℤ) :
    BilinearMap (H.X n) (H.X m) (H.X (n + m)) where
  app := internalHomMulApp hH n m
  map_smul_left U r a b := by
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [internalHomMulApp_app, hH.sectionsEquiv_smul, hH.sectionsEquiv_smul,
      internalHomMulApp_app]
  map_smul_right U r a b := by
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [internalHomMulApp_app, hH.sectionsEquiv_smul,
      (hH.sectionsEquiv n U.unop a).map_smul, hH.sectionsEquiv_smul, internalHomMulApp_app]
  naturality {U V} f a b := by
    change (H.X (n + m)).val.map f (internalHomMulApp hH n m U a b) =
      internalHomMulApp hH n m V (restrictSection (H.X n) f a) (restrictSection (H.X m) f b)
    refine hH.sections_ext (U := V.unop) fun i j hij W x => ?_
    have hab := hH.sectionsEquiv_naturality (n + m) f.unop
      (internalHomMulApp hH n m U a b) i j hij W
    rw [Quiver.Hom.op_unop] at hab
    have hb : (hH.sectionsEquiv m V.unop (restrictSection (H.X m) f b)).app i (i + m) rfl W =
        (hH.sectionsEquiv m U.unop b).app i (i + m) rfl (Over.mk (W.hom ≫ f.unop)) := by
      have h := hH.sectionsEquiv_naturality m f.unop b i (i + m) rfl W
      rw [Quiver.Hom.op_unop] at h
      exact h
    have ha : (hH.sectionsEquiv n V.unop (restrictSection (H.X n) f a)).app (i + m) j
          (by omega) W =
        (hH.sectionsEquiv n U.unop a).app (i + m) j (by omega) (Over.mk (W.hom ≫ f.unop)) := by
      have h := hH.sectionsEquiv_naturality n f.unop a (i + m) j (by omega) W
      rw [Quiver.Hom.op_unop] at h
      exact h
    refine (DFunLike.congr_fun hab x).trans
      ((internalHomMulApp_app hH n m U a b hij (Over.mk (W.hom ≫ f.unop)) x).trans
        (Eq.symm ((internalHomMulApp_app hH n m V (restrictSection (H.X n) f a)
          (restrictSection (H.X m) f b) hij W x).trans ?_)))
    exact (DFunLike.congr_fun ha _).trans
      (DFunLike.congr_arg ((hH.sectionsEquiv n U.unop a).app (i + m) j (by omega)
        (Over.mk (W.hom ≫ f.unop))) (DFunLike.congr_fun hb x))

/-- The multiplication of the endomorphism algebra names the composition of local
endomorphisms. -/
theorem internalHomMul_sectionsEquiv (hH : IsInternalHom N N H) (n m : ℤ) (U : C)
    (a : (H.X n).val.obj (Opposite.op U)) (b : (H.X m).val.obj (Opposite.op U)) :
    hH.sectionsEquiv (n + m) U ((internalHomMul hH n m).app (Opposite.op U) a b) =
      LocalHom.comp (hH.sectionsEquiv m U b) (hH.sectionsEquiv n U a) (add_comm m n) :=
  Equiv.apply_symm_apply _ _

/-- The product of two sections of the endomorphism algebra, on local sections of `N`, computed
through an arbitrary intermediate degree. -/
theorem internalHom_mul_app (hH : IsInternalHom N N H) (n m : ℤ) (U : C)
    (a : (H.X n).val.obj (Opposite.op U)) (b : (H.X m).val.obj (Opposite.op U))
    (i j k : ℤ) (hik : i + (n + m) = k) (hij : i + m = j) (hjk : j + n = k) (V : Over U)
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (hH.sectionsEquiv (n + m) U ((internalHomMul hH n m).app (Opposite.op U) a b)).app i k hik
        V x =
      (hH.sectionsEquiv n U a).app j k hjk V ((hH.sectionsEquiv m U b).app i j hij V x) := by
  rw [internalHomMul_sectionsEquiv]
  exact localHom_comp_sections_app hH a b hik j hij hjk V x

/-- The differential of the endomorphism algebra, on local sections of `N`. -/
theorem internalHom_d_app (hH : IsInternalHom N N H) (n : ℤ) (U : C)
    (a : (H.X n).val.obj (Opposite.op U)) (i j k l : ℤ) (hij : i + (n + 1) = j)
    (hik : i + n = k) (hil : i + 1 = l) (V : Over U)
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (hH.sectionsEquiv (n + 1) U ((H.d n (n + 1)).val.app (Opposite.op U) a)).app i j hij V x =
      (N.complex.d k j).val.app (Opposite.op V.left)
          ((hH.sectionsEquiv n U a).app i k hik V x) +
        (Int.negOnePow (n + 1) : ℤ) •
          (hH.sectionsEquiv n U a).app l j (by omega) V
            ((N.complex.d i l).val.app (Opposite.op V.left) x) := by
  rw [hH.sectionsEquiv_d]
  unfold localDiffApp
  subst hik
  subst hil
  have aux (p : ℤ) (hp : i + (n + 1) - n = p) :
      (hH.sectionsEquiv n U a).app (i + (n + 1) - n) j (by omega) V
          ((N.complex.d i (i + (n + 1) - n)).val.app (Opposite.op V.left) x) =
        (hH.sectionsEquiv n U a).app p j (by omega) V
          ((N.complex.d i p).val.app (Opposite.op V.left) x) := by
    subst hp
    rfl
  exact congrArg (fun y => (N.complex.d (i + n) j).val.app (Opposite.op V.left)
      ((hH.sectionsEquiv n U a).app i (i + n) rfl V x) +
      (Int.negOnePow (n + 1) : ℤ) • y) (aux (i + 1) (by omega))

/-- Transporting a section of an internal hom along an equality of degrees does not change the
local endomorphism it names. -/
theorem internalHom_sectionsEquiv_cast_app (hH : IsInternalHom N N H) {n m : ℤ}
    (h : n = m) (U : C) (p : (H.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + m = j)
    (V : Over U) (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (hH.sectionsEquiv m U (gradedCast (fun q => (H.X q).val.obj (Opposite.op U)) h p)).app
        i j hij V x =
      (hH.sectionsEquiv n U p).app i j (by omega) V x := by
  cases h
  rfl

/-- The identification of sections of an internal hom with local homomorphisms is compatible with
integer multiples. -/
theorem internalHom_sectionsEquiv_zsmul (hH : IsInternalHom N N H) (n : ℤ) (U : C)
    (r : ℤ) (p : (H.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (hH.sectionsEquiv n U (r • p)).app i j hij V x =
      r • (hH.sectionsEquiv n U p).app i j hij V x := by
  let f : (H.X n).val.obj (Opposite.op U) →+
      (N.complex.X j).val.obj (Opposite.op V.left) :=
    { toFun := fun q => (hH.sectionsEquiv n U q).app i j hij V x
      map_zero' := hH.sectionsEquiv_zero n U i j hij V x
      map_add' := fun q q' => hH.sectionsEquiv_add n U q q' i j hij V x }
  exact map_zsmul f r p

/-- The sheaf of differential graded `R`-algebras carried by a complex which is an internal hom
of a right differential graded `B`-module `N` with itself: the multiplication is composition of
local endomorphisms and the unit is the identity. -/
noncomputable def endomorphismAlgebraOfIsInternalHom (hH : IsInternalHom N N H) :
    DifferentialGradedAlgebra.{t, s} R where
  complex := H
  mul := internalHomMul hH
  one := internalHomOne hH
  mul_assoc n m k U a b c := by
    apply heq_of_gradedCast_eq (F := fun q => (H.X q).val.obj U) (add_assoc n m k)
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [internalHom_sectionsEquiv_cast_app,
      internalHom_mul_app hH (n + m) k U.unop _ c i (i + k) j (by omega) rfl (by omega),
      internalHom_mul_app hH n m U.unop a b (i + k) (i + k + m) j (by omega) rfl (by omega),
      internalHom_mul_app hH n (m + k) U.unop a _ i (i + k + m) j (by omega) (by omega)
        (by omega),
      internalHom_mul_app hH m k U.unop b c i (i + k) (i + k + m) (by omega) rfl (by omega)]
  one_mul n U a := by
    apply heq_of_gradedCast_eq (F := fun q => (H.X q).val.obj U) (zero_add n)
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [internalHom_sectionsEquiv_cast_app,
      internalHom_mul_app hH 0 n U.unop _ a i j j (by omega) hij (by omega),
      internalHomOne_eval, localHom_id_app_self]
  mul_one n U a := by
    apply heq_of_gradedCast_eq (F := fun q => (H.X q).val.obj U) (add_zero n)
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [internalHom_sectionsEquiv_cast_app,
      internalHom_mul_app hH n 0 U.unop a _ i i j (by omega) (by omega) hij,
      internalHomOne_eval, localHom_id_app_self]
  leibniz n m U a b := by
    refine hH.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [hH.sectionsEquiv_add, internalHom_sectionsEquiv_zsmul,
      internalHom_sectionsEquiv_cast_app, internalHom_sectionsEquiv_cast_app,
      internalHom_d_app hH (n + m) U.unop _ i j (i + m + n) (i + 1) (by omega) (by omega)
        (by omega),
      internalHom_mul_app hH (n + 1) m U.unop _ b i (i + m) j (by omega) rfl (by omega),
      internalHom_mul_app hH n (m + 1) U.unop a _ i (i + m + 1) j (by omega) (by omega)
        (by omega),
      internalHom_mul_app hH n m U.unop a b i (i + m) (i + m + n) (by omega) rfl (by omega),
      internalHom_mul_app hH n m U.unop a b (i + 1) (i + m + 1) j (by omega) (by omega)
        (by omega),
      internalHom_d_app hH n U.unop a (i + m) j (i + m + n) (i + m + 1) (by omega) (by omega)
        (by omega),
      internalHom_d_app hH m U.unop b i (i + m + 1) (i + m) (i + 1) (by omega) (by omega)
        (by omega)]
    simp only [map_add, map_zsmul, smul_add, smul_smul]
    simp only [Int.negOnePow_add, Units.val_mul, Units.val_neg, neg_smul, mul_neg,
      Int.negOnePow_one, mul_one]
    abel

/-- The underlying complex of the endomorphism algebra built on an internal hom is that
internal hom. -/
@[simp]
theorem endomorphismAlgebraOfIsInternalHom_complex (hH : IsInternalHom N N H) :
    (endomorphismAlgebraOfIsInternalHom hH).complex = H := rfl

/-- The sheafified differential graded endomorphisms of a right differential graded `B`-module
`N` carry a differential graded `R`-algebra structure, with composition of local endomorphisms
as multiplication and the identity as unit. -/
@[stacks 0FRR "the differential graded endomorphism algebra"]
noncomputable def isEndomorphismAlgebra_endomorphismAlgebraOfIsInternalHom
    (hH : IsInternalHom N N H) :
    IsEndomorphismAlgebra N (endomorphismAlgebraOfIsInternalHom hH) where
  isInternalHom := hH
  mul_spec n m U a b := internalHomMul_sectionsEquiv hH n m U a b
  one_spec U _ _ hij V x := internalHomOne_app hH U hij V x

end EndomorphismAlgebra

/-! ### Unital homomorphisms and compatible bimodule structures -/

/-- A homomorphism of sheaves of differential graded `R`-algebras which preserves the identity on
every object of the site. -/
structure UnitalHom (A E : DifferentialGradedAlgebra.{t, a} R) where
  /-- The underlying homomorphism of sheaves of differential graded algebras. -/
  toHom : A ⟶ E
  /-- The identity is preserved on every object of the site. -/
  map_one (U : C) :
    (toHom.toHomologicalComplex.f 0).val.app (Opposite.op U) (A.one.eval (Opposite.op U)) =
      E.one.eval (Opposite.op U)

/-- An `(A, B)`-bimodule structure on a right differential graded `B`-module `N` compatible with
the given right `B`-action: a left `A`-action on the same complex which is associative and
unital, commutes with the right `B`-action, and obeys the signed Leibniz rule. -/
@[sga "6 IV 2.6" "more general"]
structure BimoduleStructure (A : DifferentialGradedAlgebra.{t, a} R)
    (N : DifferentialGradedModule.{t, a, w} B) where
  /-- Left multiplication by homogeneous sections of `A`. -/
  leftMul (n m : ℤ) : BilinearMap (A.complex.X n) (N.complex.X m) (N.complex.X (n + m))
  /-- The left action is associative. -/
  left_assoc (i j n : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
      (a' : (A.complex.X j).val.obj U) (x : (N.complex.X n).val.obj U) :
    HEq ((leftMul i (j + n)).app U a ((leftMul j n).app U a' x))
      ((leftMul (i + j) n).app U ((A.mul i j).app U a a') x)
  /-- Left and right multiplication commute. -/
  left_right_assoc (i n j : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
      (x : (N.complex.X n).val.obj U) (b : (B.complex.X j).val.obj U) :
    HEq ((N.mul (i + n) j).app U ((leftMul i n).app U a x) b)
      ((leftMul i (n + j)).app U a ((N.mul n j).app U x b))
  /-- The unit of `A` acts as the identity. -/
  one_left (n : ℤ) (U : Cᵒᵖ) (x : (N.complex.X n).val.obj U) :
    HEq ((leftMul 0 n).app U (A.one.eval U) x) x
  /-- The left action obeys the signed Leibniz rule. -/
  leibniz_left (n m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U)
      (x : (N.complex.X m).val.obj U) :
    (N.complex.d (n + m) (n + m + 1)).val.app U ((leftMul n m).app U a x) =
      gradedCast (fun q ↦ (N.complex.X q).val.obj U) (add_right_comm n 1 m)
          ((leftMul (n + 1) m).app U ((A.complex.d n (n + 1)).val.app U a) x) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (N.complex.X q).val.obj U) (add_assoc n m 1).symm
            ((leftMul n (m + 1)).app U a ((N.complex.d m (m + 1)).val.app U x))

namespace BimoduleStructure

/-- A compatible bimodule structure on `N` makes `N` a differential graded `(A, B)`-bimodule. -/
def toBimodule {N : DifferentialGradedModule.{t, a, w} B} (s : BimoduleStructure A N) :
    DifferentialGradedBimodule.{t, a, w} A B where
  complex := N.complex
  rightMul := N.mul
  leftMul := s.leftMul
  left_assoc := s.left_assoc
  right_assoc := N.mul_assoc
  left_right_assoc := s.left_right_assoc
  one_left := s.one_left
  one_right := N.mul_one
  leibniz_left := s.leibniz_left
  leibniz_right := N.leibniz

/-- The bimodule attached to a compatible bimodule structure has the same underlying complex. -/
@[simp]
theorem toBimodule_complex {N : DifferentialGradedModule.{t, a, w} B}
    (s : BimoduleStructure A N) : s.toBimodule.complex = N.complex := rfl

/-- The left multiplication of the attached bimodule is the one given by the bimodule
structure. -/
@[simp]
theorem toBimodule_leftMul {N : DifferentialGradedModule.{t, a, w} B}
    (s : BimoduleStructure A N) (n m : ℤ) : s.toBimodule.leftMul n m = s.leftMul n m := rfl

end BimoduleStructure

/-! ### The correspondence

A compatible bimodule structure on `N` and an identity-preserving homomorphism
`A ⟶ SheafHom^dg_B(N, N)` are the same datum. -/

section Correspondence

variable {N : DifferentialGradedModule.{t, a, w} B} {E : DifferentialGradedAlgebra.{t, a} R}

/-- Left multiplication by a local section of `A`, as a map on local sections of `N`. -/
noncomputable def leftActionApp (s : BimoduleStructure A N) (n i j : ℤ) (hij : i + n = j)
    (U : C) (V : Over U) (a : (A.complex.X n).val.obj (Opposite.op U)) :
    (N.complex.X i).val.obj (Opposite.op V.left) →+
      (N.complex.X j).val.obj (Opposite.op V.left) :=
  gradedCast (fun q => (N.complex.X i).val.obj (Opposite.op V.left) →+
    (N.complex.X q).val.obj (Opposite.op V.left)) (by omega)
      ((s.leftMul n i).app (Opposite.op V.left)
        (restrictSection (A.complex.X n) V.hom.op a))

/-- Left multiplication by a local section of `A`, read off in the degree it naturally lands
in. -/
theorem leftActionApp_heq (s : BimoduleStructure A N) (n i j : ℤ) (hij : i + n = j)
    (U : C) (V : Over U) (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    HEq (leftActionApp s n i j hij U V a x)
      ((s.leftMul n i).app (Opposite.op V.left)
        (restrictSection (A.complex.X n) V.hom.op a) x) := by
  have h : n + i = j := by omega
  subst h
  rfl

/-- Left multiplication by a local section of `A`, in the degree the left action lands in. -/
theorem leftActionApp_apply (s : BimoduleStructure A N) (n i : ℤ) (hij : i + n = n + i)
    (U : C) (V : Over U) (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    leftActionApp s n i (n + i) hij U V a x =
      (s.leftMul n i).app (Opposite.op V.left)
        (restrictSection (A.complex.X n) V.hom.op a) x :=
  eq_of_heq (leftActionApp_heq s n i (n + i) hij U V a x)

/-- Left multiplication by a local section of `A` is left multiplication followed by the
transport along the equality of degrees. -/
theorem leftActionApp_apply_cast (s : BimoduleStructure A N) (n i j : ℤ)
    (hij : i + n = j) (U : C) (V : Over U) (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    leftActionApp s n i j hij U V a x =
      gradedCast (fun q => (N.complex.X q).val.obj (Opposite.op V.left)) (by omega)
        ((s.leftMul n i).app (Opposite.op V.left)
          (restrictSection (A.complex.X n) V.hom.op a) x) := by
  have h : n + i = j := by omega
  subst h
  rfl

/-- Left multiplication by a local section of `A`, as a degree-`n` local endomorphism of `N`. -/
noncomputable def leftAction (s : BimoduleStructure A N) (n : ℤ) (U : C)
    (a : (A.complex.X n).val.obj (Opposite.op U)) : LocalHom N N n U where
  app i j hij V := leftActionApp s n i j hij U V a
  map_smul i j hij V r x := by
    have h : n + i = j := by omega
    subst h
    rw [leftActionApp_apply, leftActionApp_apply]
    exact (s.leftMul n i).map_smul_right _ r _ x
  naturality i j hij {V W} g x := by
    have h : n + i = j := by omega
    subst h
    change restrictSection (N.complex.X (n + i)) g.left.op
        (leftActionApp s n i (n + i) hij U V a x) =
      leftActionApp s n i (n + i) hij U W a (restrictSection (N.complex.X i) g.left.op x)
    rw [leftActionApp_apply, leftActionApp_apply, restrictSection_bilinearMap,
      ← restrictSection_comp,
      show V.hom.op ≫ g.left.op = W.hom.op from congrArg Quiver.Hom.op (Over.w g)]
  isLinear i j hij p V x b := by
    have h : n + i = j := by omega
    subst h
    rw [leftActionApp_apply]
    refine eq_of_heq ((leftActionApp_heq s n (i + p) (n + i + p) (by omega) U V a
      ((N.mul i p).app (Opposite.op V.left) x b)).trans ?_)
    exact (s.left_right_assoc n i p (Opposite.op V.left)
      (restrictSection (A.complex.X n) V.hom.op a) x b).symm

/-- The local endomorphism of `N` attached to a local section of `A` acts by left
multiplication. -/
theorem leftAction_app (s : BimoduleStructure A N) (n i j : ℤ) (hij : i + n = j)
    (U : C) (V : Over U) (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    HEq ((leftAction s n U a).app i j hij V x)
      ((s.leftMul n i).app (Opposite.op V.left)
        (restrictSection (A.complex.X n) V.hom.op a) x) :=
  leftActionApp_heq s n i j hij U V a x

/-- The section of the endomorphism algebra given by left multiplication by a local section
of `A`. -/
noncomputable def actionSection (s : BimoduleStructure A N) (hE : IsEndomorphismAlgebra N E) (n : ℤ)
    (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U) : (E.complex.X n).val.obj U :=
  (hE.isInternalHom.sectionsEquiv n U.unop).symm (leftAction s n U.unop a)

/-- The section of the endomorphism algebra attached to a local section of `A` names the local
endomorphism given by left multiplication. -/
theorem actionSection_app (s : BimoduleStructure A N) (hE : IsEndomorphismAlgebra N E)
    (n i j : ℤ) (hij : i + n = j) (U : C) (V : Over U)
    (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    HEq ((hE.isInternalHom.sectionsEquiv n U
        (actionSection s hE n (Opposite.op U) a)).app i j hij V x)
      ((s.leftMul n i).app (Opposite.op V.left)
        (restrictSection (A.complex.X n) V.hom.op a) x) := by
  unfold actionSection
  rw [Equiv.apply_symm_apply]
  exact leftAction_app s n i j hij U V a x

/-- The section of the endomorphism algebra attached to a local section of `A`, read off in the
degree the left action lands in. -/
theorem actionSection_app_self (s : BimoduleStructure A N) (hE : IsEndomorphismAlgebra N E)
    (n i : ℤ) (hij : i + n = n + i) (U : C) (V : Over U)
    (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    (hE.isInternalHom.sectionsEquiv n U
        (actionSection s hE n (Opposite.op U) a)).app i (n + i) hij V x =
      (s.leftMul n i).app (Opposite.op V.left)
        (restrictSection (A.complex.X n) V.hom.op a) x :=
  eq_of_heq (actionSection_app s hE n i (n + i) hij U V a x)

/-- Left multiplication by sections of `A` of a fixed degree, as a morphism of sheaves of
modules into the endomorphism algebra. -/
noncomputable def actionHomComponent (s : BimoduleStructure A N) (hE : IsEndomorphismAlgebra N E)
    (n : ℤ) : A.complex.X n ⟶ E.complex.X n where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := actionSection s hE n U
          map_add' := by
            intro a b
            refine hE.isInternalHom.sections_ext (U := U.unop) fun i j hij V x => ?_
            have h : n + i = j := by omega
            subst h
            rw [hE.isInternalHom.sectionsEquiv_add, actionSection_app_self,
              actionSection_app_self, actionSection_app_self, restrictSection_add,
              Stacks.BilinearMap.map_add_left]
          map_smul' := by
            intro r a
            refine hE.isInternalHom.sections_ext (U := U.unop) fun i j hij V x => ?_
            have h : n + i = j := by omega
            subst h
            rw [hE.isInternalHom.sectionsEquiv_smul, actionSection_app_self,
              actionSection_app_self, restrictSection_smul, (s.leftMul n i).map_smul_left]
            rfl }
      naturality {U V} f := by
        ext a
        change actionSection s hE n V (restrictSection (A.complex.X n) f a) =
          restrictSection (E.complex.X n) f (actionSection s hE n U a)
        refine hE.isInternalHom.sections_ext (U := V.unop) fun i j hij W x => ?_
        have h : n + i = j := by omega
        subst h
        have hn : (hE.isInternalHom.sectionsEquiv n V.unop
              (restrictSection (E.complex.X n) f (actionSection s hE n U a))).app i (n + i)
              hij W =
            (hE.isInternalHom.sectionsEquiv n U.unop (actionSection s hE n U a)).app i (n + i)
              hij (Over.mk (W.hom ≫ f.unop)) :=
          hE.isInternalHom.sectionsEquiv_naturality n f.unop (actionSection s hE n U a) i
            (n + i) hij W
        rw [DFunLike.congr_fun hn x, actionSection_app_self, actionSection_app_self,
          ← restrictSection_comp,
          show f ≫ W.hom.op = (W.hom ≫ f.unop).op from rfl]
        rfl }

/-- Left multiplication by local sections of `A` commutes with the differentials of `A` and of
the endomorphism algebra. -/
theorem actionSection_d (s : BimoduleStructure A N) (hE : IsEndomorphismAlgebra N E)
    (n : ℤ) (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U) :
    actionSection s hE (n + 1) U ((A.complex.d n (n + 1)).val.app U a) =
      (E.complex.d n (n + 1)).val.app U (actionSection s hE n U a) := by
  refine hE.isInternalHom.sections_ext fun i j hij V x => ?_
  have hj : n + i + 1 = j := by omega
  subst hj
  rw [internalHom_d_app hE.isInternalHom n U.unop _ i (n + i + 1) (n + i) (i + 1)
      (by omega) (by omega) (by omega),
    actionSection_app_self s hE n i (by omega) U.unop V a x]
  simp only [actionSection, Equiv.apply_symm_apply, leftAction, leftActionApp_apply_cast]
  have h := s.leibniz_left n i (Opposite.op V.left)
    (restrictSection (A.complex.X n) V.hom.op a) x
  rw [← restrictSection_val_app] at h
  rw [h]
  simp only [Int.negOnePow_succ, Units.val_neg, neg_smul]
  abel

/-- Left multiplication by local sections of `A` is a homomorphism of sheaves of differential
graded algebras `A ⟶ SheafHom^dg_B(N, N)`. -/
noncomputable def actionAlgebraHom (s : BimoduleStructure A N)
    (hE : IsEndomorphismAlgebra N E) : A ⟶ E where
  toHomologicalComplex :=
    { f := actionHomComponent s hE
      comm' n m _ := by
        by_cases h : n + 1 = m
        · subst h
          ext U a
          exact (actionSection_d s hE n U a).symm
        · rw [A.complex.shape n m h, E.complex.shape n m h]
          simp }
  map_mul n m U a b := by
    change actionSection s hE (n + m) U ((A.mul n m).app U a b) =
      (E.mul n m).app U (actionSection s hE n U a) (actionSection s hE m U b)
    refine hE.isInternalHom.sections_ext (U := U.unop) fun i j hij V x => ?_
    rw [hE.mul_spec,
      localHom_comp_sections_app hE.isInternalHom _ _ hij (m + i) (by omega) (by omega) V x]
    simp only [actionSection, Equiv.apply_symm_apply]
    have hj : n + m + i = j := by omega
    subst hj
    apply eq_of_heq
    refine (leftAction_app s (n + m) i (n + m + i) (by omega) U.unop V _ x).trans ?_
    rw [restrictSection_bilinearMap]
    exact (s.left_assoc n m i _ _ _ x).symm.trans
      (leftAction_app s n (m + i) (n + m + i) (by omega) U.unop V a
        ((s.leftMul m i).app (Opposite.op V.left)
          (restrictSection (A.complex.X m) V.hom.op b) x)).symm

/-- Left multiplication by the unit of `A` is the unit of the endomorphism algebra. -/
theorem actionSection_one (s : BimoduleStructure A N) (hE : IsEndomorphismAlgebra N E) (U : C) :
    actionSection s hE 0 (Opposite.op U) (A.one.eval (Opposite.op U)) =
      E.one.eval (Opposite.op U) := by
  refine hE.isInternalHom.sections_ext (U := U) fun i j hij V x => ?_
  apply eq_of_heq
  refine (actionSection_app s hE 0 i j hij U V _ x).trans ?_
  have hn : restrictSection (A.complex.X 0) V.hom.op (A.one.eval (Opposite.op U)) =
      A.one.eval (Opposite.op V.left) := A.one.property V.hom.op
  rw [hn]
  exact (s.one_left i _ x).trans (hE.one_spec U i j hij V x).symm

/-- The identity-preserving homomorphism `A ⟶ SheafHom^dg_B(N, N)` attached to a compatible
bimodule structure on `N`: it sends a local section of `A` to left multiplication by it. -/
noncomputable def actionHom (s : BimoduleStructure A N) (hE : IsEndomorphismAlgebra N E) :
    UnitalHom A E where
  toHom := actionAlgebraHom s hE
  map_one U := actionSection_one s hE U

/-- A local endomorphism takes the same value over `W ⟶ U` however that morphism is written. -/
theorem localHom_app_id_comp {n : ℤ} {U W : C} (f : LocalHom N N n U) (g : W ⟶ U)
    (i j : ℤ) (hij : i + n = j) (x : (N.complex.X i).val.obj (Opposite.op W)) :
    f.app i j hij (Over.mk (𝟙 W ≫ g)) x = f.app i j hij (Over.mk g) x := by
  let ev : (W ⟶ U) → (N.complex.X j).val.obj (Opposite.op W) :=
    fun k => f.app i j hij (Over.mk k) x
  exact congrArg ev (Category.id_comp g)

/-- The local endomorphism named by a restricted section, over the identity, is the one named by
the section, over the restricting morphism. -/
private theorem sectionsEquiv_restrict_app_id {H : CochainComplex (SheafOfModules.{s} R) ℤ}
    (hH : IsInternalHom N N H) (n : ℤ) {U V : C} (f : V ⟶ U) (a : (H.X n).val.obj (Opposite.op U))
    (i j : ℤ) (hij : i + n = j) :
    (hH.sectionsEquiv n V (restrictSection (H.X n) f.op a)).app i j hij (Over.mk (𝟙 V)) =
      (hH.sectionsEquiv n U a).app i j hij (Over.mk f) := by
  refine AddMonoidHom.ext fun x => ?_
  exact (DFunLike.congr_fun (hH.sectionsEquiv_naturality n f a i j hij (Over.mk (𝟙 V))) x).trans
    (localHom_app_id_comp _ f i j hij x)

/-- Evaluating a section of an internal hom on the whole of `U` is compatible with restriction. -/
theorem internalHom_eval_restrict {H : CochainComplex (SheafOfModules.{s} R) ℤ}
    (hH : IsInternalHom N N H) (n : ℤ) {U V : C} (f : V ⟶ U)
    (a : (H.X n).val.obj (Opposite.op U)) (i j : ℤ) (hij : i + n = j)
    (x : (N.complex.X i).val.obj (Opposite.op U)) :
    restrictSection (N.complex.X j) f.op
        ((hH.sectionsEquiv n U a).app i j hij (Over.mk (𝟙 U)) x) =
      (hH.sectionsEquiv n V (restrictSection (H.X n) f.op a)).app i j hij (Over.mk (𝟙 V))
        (restrictSection (N.complex.X i) f.op x) := by
  rw [sectionsEquiv_restrict_app_id]
  exact (hH.sectionsEquiv n U a).naturality i j hij
    (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 U)) x

/-- The left action of `A` on `N` attached to an identity-preserving homomorphism
`A ⟶ SheafHom^dg_B(N, N)`: a local section of `A` acts by the local endomorphism it names. -/
noncomputable def homLeftMul (hE : IsEndomorphismAlgebra N E) (f : UnitalHom A E) (n m : ℤ) :
    BilinearMap (A.complex.X n) (N.complex.X m) (N.complex.X (n + m)) where
  app U :=
    { toFun := fun a => (hE.isInternalHom.sectionsEquiv n U.unop
        ((f.toHom.toHomologicalComplex.f n).val.app U a)).app m (n + m) (by omega)
          (Over.mk (𝟙 U.unop))
      map_zero' := by
        ext x
        simp only [map_zero, IsInternalHom.sectionsEquiv_zero]
        rfl
      map_add' := by
        intro a b
        ext x
        simp only [map_add, hE.isInternalHom.sectionsEquiv_add, AddMonoidHom.add_apply] }
  map_smul_left U r a x := by
    change (hE.isInternalHom.sectionsEquiv n U.unop
      ((f.toHom.toHomologicalComplex.f n).val.app U (r • a))).app _ _ _ _ _ = _
    rw [map_smul, hE.isInternalHom.sectionsEquiv_smul]
    simp
  map_smul_right U r a x :=
    (hE.isInternalHom.sectionsEquiv n U.unop
      ((f.toHom.toHomologicalComplex.f n).val.app U a)).map_smul m (n + m) (by omega)
        (Over.mk (𝟙 U.unop)) r x
  naturality {U V} g a x := by
    change restrictSection (N.complex.X (n + m)) g
        ((hE.isInternalHom.sectionsEquiv n U.unop
          ((f.toHom.toHomologicalComplex.f n).val.app U a)).app m (n + m) (by omega)
            (Over.mk (𝟙 U.unop)) x) =
      (hE.isInternalHom.sectionsEquiv n V.unop
        ((f.toHom.toHomologicalComplex.f n).val.app V
          (restrictSection (A.complex.X n) g a))).app m (n + m) (by omega)
          (Over.mk (𝟙 V.unop)) (restrictSection (N.complex.X m) g x)
    have h := internalHom_eval_restrict hE.isInternalHom n g.unop
      ((f.toHom.toHomologicalComplex.f n).val.app U a) m (n + m) (by omega) x
    rw [Quiver.Hom.op_unop, restrictSection_val_app] at h
    exact h

/-- The left action of `A` attached to a homomorphism into the endomorphism algebra, on local
sections. -/
theorem homLeftMul_app (hE : IsEndomorphismAlgebra N E) (f : UnitalHom A E) (n m : ℤ)
    (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U) (x : (N.complex.X m).val.obj U) :
    (homLeftMul hE f n m).app U a x =
      (hE.isInternalHom.sectionsEquiv n U.unop
        ((f.toHom.toHomologicalComplex.f n).val.app U a)).app m (n + m) (by omega)
          (Over.mk (𝟙 U.unop)) x := rfl

/-- The left action of `A` attached to a homomorphism into the endomorphism algebra, on local
sections over an object of the site. -/
theorem homLeftMul_app_op (hE : IsEndomorphismAlgebra N E) (f : UnitalHom A E) (n m : ℤ)
    (U : C) (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X m).val.obj (Opposite.op U)) :
    (homLeftMul hE f n m).app (Opposite.op U) a x =
      (hE.isInternalHom.sectionsEquiv n U
        ((f.toHom.toHomologicalComplex.f n).val.app (Opposite.op U) a)).app m (n + m) (by omega)
          (Over.mk (𝟙 U)) x := rfl

/-- Transporting the value of a local endomorphism along an equality of degrees is the value in
the other degree. -/
theorem localHom_top_app_cast {n : ℤ} {U : Cᵒᵖ} (f : LocalHom N N n U.unop)
    (i j k : ℤ) (hij : i + n = j) (hjk : j = k) (x : (N.complex.X i).val.obj U) :
    gradedCast (fun q => (N.complex.X q).val.obj U) hjk
        (f.app i j hij (Over.mk (𝟙 U.unop)) x) =
      f.app i k (by omega) (Over.mk (𝟙 U.unop)) x := by
  subst hjk
  rfl

/-- The compatible bimodule structure on `N` attached to an identity-preserving homomorphism
`A ⟶ SheafHom^dg_B(N, N)`. -/
noncomputable def homBimoduleStructure (hE : IsEndomorphismAlgebra N E) (f : UnitalHom A E) :
    BimoduleStructure A N where
  leftMul := homLeftMul hE f
  left_assoc n m i U a b x := by
    apply heq_of_gradedCast_eq (F := fun q => (N.complex.X q).val.obj U) (add_assoc n m i).symm
    simp only [homLeftMul_app]
    rw [localHom_top_app_cast, f.toHom.map_mul, hE.mul_spec,
      localHom_comp_sections_app hE.isInternalHom _ _ (by omega) (m + i) (by omega) (by omega)
        (Over.mk (𝟙 U.unop)) x]
  left_right_assoc n i m U a x b := by
    apply heq_of_gradedCast_eq (F := fun q => (N.complex.X q).val.obj U) (add_assoc n i m)
    simp only [homLeftMul_app]
    have h := (hE.isInternalHom.sectionsEquiv n U.unop
      ((f.toHom.toHomologicalComplex.f n).val.app U a)).isLinear i (n + i)
        (by omega) m (Over.mk (𝟙 U.unop)) x b
    change _ = (N.mul (n + i) m).app U _ b at h
    rw [← h, localHom_top_app_cast]
    rfl
  one_left i U x := by
    rw [homLeftMul_app, f.map_one]
    exact hE.one_spec U.unop i (0 + i) (by omega) (Over.mk (𝟙 U.unop)) x
  leibniz_left n i U a x := by
    simp only [homLeftMul_app]
    rw [localHom_top_app_cast, localHom_top_app_cast]
    have h := internalHom_d_app hE.isInternalHom n U.unop
      ((f.toHom.toHomologicalComplex.f n).val.app U a)
      i (n + i + 1) (n + i) (i + 1) (by omega) (by omega) (by omega)
      (Over.mk (𝟙 U.unop)) x
    have hc := congrArg (fun k => k.val.app U a)
      (f.toHom.toHomologicalComplex.comm n (n + 1))
    change (E.complex.d n (n + 1)).val.app U
        ((f.toHom.toHomologicalComplex.f n).val.app U a) =
      (f.toHom.toHomologicalComplex.f (n + 1)).val.app U
        ((A.complex.d n (n + 1)).val.app U a) at hc
    rw [hc] at h
    dsimp only [Over.mk_left, Opposite.op_unop] at h
    simp only [Int.negOnePow_succ, Units.val_neg, neg_smul] at h
    rw [← sub_eq_add_neg] at h
    exact (eq_sub_iff_add_eq.mp h).symm

/-- The bimodule structure attached to a homomorphism into the endomorphism algebra acts on
local sections by the local endomorphism named by the image of a section of `A`. -/
theorem homBimoduleStructure_app (hE : IsEndomorphismAlgebra N E) (f : UnitalHom A E)
    (n i j : ℤ) (hij : i + n = j) (U : C) (V : Over U)
    (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    HEq ((hE.isInternalHom.sectionsEquiv n U
        ((f.toHom.toHomologicalComplex.f n).val.app (Opposite.op U) a)).app i j hij V x)
      (((homBimoduleStructure hE f).leftMul n i).app (Opposite.op V.left)
        (restrictSection (A.complex.X n) V.hom.op a) x) := by
  show HEq _ ((homLeftMul hE f n i).app (Opposite.op V.left)
    (restrictSection (A.complex.X n) V.hom.op a) x)
  rw [homLeftMul_app_op, ← restrictSection_val_app]
  rw [sectionsEquiv_restrict_app_id]
  have hj : n + i = j := by omega
  subst hj
  exact HEq.rfl

/-- A compatible bimodule structure is determined by its left multiplication. -/
theorem BimoduleStructure.ext {s t : BimoduleStructure A N}
    (h : s.leftMul = t.leftMul) : s = t := by
  cases s
  cases t
  cases h
  rfl

/-- An identity-preserving homomorphism is determined by its underlying homomorphism. -/
theorem UnitalHom.ext {f g : UnitalHom A E} (h : f.toHom = g.toHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Passing from a compatible bimodule structure to a homomorphism into the endomorphism algebra
and back recovers the structure. -/
theorem homBimoduleStructure_actionHom (hE : IsEndomorphismAlgebra N E)
    (s : BimoduleStructure A N) : homBimoduleStructure hE (actionHom s hE) = s := by
  apply BimoduleStructure.ext
  funext n i
  refine Stacks.BilinearMap.ext fun U a x => ?_
  show (homLeftMul hE (actionHom s hE) n i).app U a x = _
  rw [homLeftMul_app]
  have h := eq_of_heq (actionSection_app s hE n i (n + i) (by omega) U.unop
    (Over.mk (𝟙 U.unop)) a x)
  rw [show (Over.mk (𝟙 U.unop)).hom.op = 𝟙 U from rfl, restrictSection_id] at h
  exact h

/-- Passing from a homomorphism into the endomorphism algebra to a compatible bimodule structure
and back recovers the homomorphism. -/
theorem actionHom_homBimoduleStructure (hE : IsEndomorphismAlgebra N E)
    (f : UnitalHom A E) : actionHom (homBimoduleStructure hE f) hE = f := by
  apply UnitalHom.ext
  refine DifferentialGradedAlgebra.Hom.ext fun n => ?_
  ext U a
  refine hE.isInternalHom.sections_ext fun i j hij V x => ?_
  exact eq_of_heq
    ((actionSection_app (homBimoduleStructure hE f) hE n i j hij U.unop V a x).trans
      (homBimoduleStructure_app hE f n i j hij U.unop V a x).symm)

/-- Compatible `(A, B)`-bimodule structures on a right differential graded `B`-module `N` are in
one-to-one correspondence with identity-preserving homomorphisms of sheaves of differential
graded `R`-algebras `A ⟶ SheafHom^dg_B(N, N)`. -/
@[stacks 0FRR "bimodule structures correspond to maps into the endomorphism algebra"]
noncomputable def bimoduleStructureEquiv (hE : IsEndomorphismAlgebra N E) :
    BimoduleStructure A N ≃ UnitalHom A E where
  toFun s := actionHom s hE
  invFun := homBimoduleStructure hE
  left_inv := homBimoduleStructure_actionHom hE
  right_inv := actionHom_homBimoduleStructure hE

/-- The correspondence between compatible bimodule structures and identity-preserving
homomorphisms into the endomorphism algebra is pinned down by the requirement that the
homomorphism attached to a structure act on local sections of `N` by left multiplication for
that structure. -/
@[stacks 0FRR "bimodule structures correspond to maps into the endomorphism algebra"]
theorem bimoduleStructureEquiv_app (hE : IsEndomorphismAlgebra N E) (s : BimoduleStructure A N)
    (n i j : ℤ) (hij : i + n = j) (U : C) (V : Over U)
    (a : (A.complex.X n).val.obj (Opposite.op U))
    (x : (N.complex.X i).val.obj (Opposite.op V.left)) :
    HEq ((hE.isInternalHom.sectionsEquiv n U
        (((bimoduleStructureEquiv hE s).toHom.toHomologicalComplex.f n).val.app
          (Opposite.op U) a)).app i j hij V x)
      ((s.leftMul n i).app (Opposite.op V.left) ((A.complex.X n).val.map V.hom.op a) x) :=
  actionSection_app s hE n i j hij U V a x

end Correspondence

end SheafOfModules

end
