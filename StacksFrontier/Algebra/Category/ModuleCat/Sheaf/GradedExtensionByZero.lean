module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroBilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSliceRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of sheaves of graded modules, and its adjunction

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let
`j : (Sh(C/U), O_U) ⟶ (Sh(C), O)` be the localization morphism. Let `A` be a sheaf of graded
`O`-algebras and `A_U = j^*A` its restriction to the slice site, as constructed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSliceRestriction.lean`.

This file constructs the functor `j_! : Mod^gr(A_U) ⥤ Mod^gr(A)`, degreewise the extension by
zero of sheaves of modules, and proves the adjunction of the source:
`Hom_{Mod^gr(A)}(j_!M, N) = Hom_{Mod^gr(A_U)}(M, j^*N)`.

## Main definitions

* `SheafOfModules.gradedExtendedAction` is the right `A`-action on the degreewise extension by
  zero of a right graded `A_U`-module. In the source this is the map
  `j_!μ_{n,m} : j_!M^n × A^m → j_!M^{n+m}` obtained from the identity
  `j_!(M^n ⊗_{O_U} A^m|_U) = j_!M^n ⊗_O A^m` of Tag 0E8I.
* `SheafOfModules.gradedExtensionByZero` is **the right graded `A`-module `j_!M`**, with
  `j_!M^n = j_!(M^n)`, and `SheafOfModules.gradedExtensionByZeroFunctor` is the functor
  `j_! : Mod^gr(A_U) ⥤ Mod^gr(A)`.
* `SheafOfModules.gradedExtensionByZeroAdjunction` is the adjunction `j_! ⊣ j^*` between right
  graded `A_U`-modules and right graded `A`-modules.
* `SheafOfModules.GradedHomOfDegree.compLeft` and `compRight` compose a homogeneous
  homomorphism of degree `n` with a homomorphism of graded modules on either side.

## Main results

* `SheafOfModules.gradedExtendedAction_unit`: the extended action agrees with the action of `M`
  on the local sections supplied by the unit of the adjunction. This pins the action down, and
  every law below is proved from it.
* `SheafOfModules.gradedExtendHomEquiv`: **Tag 0FRA.** The homomorphisms `j_!M ⟶ N` of right
  graded `A`-modules are the homomorphisms `M ⟶ j^*N` of right graded `A_U`-modules; naturally
  in both variables, which is `SheafOfModules.gradedExtensionByZeroAdjunction`.
* `SheafOfModules.gradedHomOfDegreeExtendEquiv`: the same identification in the graded category,
  for the homogeneous homomorphisms of an arbitrary degree `d`, with
  `..._naturality_left` and `..._naturality_right` its naturality in `M` and in `N`.

## Implementation notes

Homogeneous homomorphisms of degree `d` are `SheafOfModules.GradedHomOfDegree` of Tag 0FR1, so
the graded hom-module `Hom_{Mod^gr(A)}(-, -)` of the source is the direct sum of these over all
degrees; the refinement of the tag to a nonzero degree is stated in each degree separately,
which carries the same information.

**Why the action needs more than the adjunction.** The adjunction identifies *linear* maps out
of `j_!M^n`, while the action is a *bilinear* map `j_!M^n × A^m → j_!M^{n+m}`. The source bridges
the gap with the identity `j_!(M^n ⊗_{O_U} A^m|_U) = j_!M^n ⊗_O A^m` of Tag 0E8I. Here the bridge
is instead the currying of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtensionByZeroBilinear.lean`, which trades the
tensor product for the internal hom of Tag 03EM: a bilinear map out of `j_!M^n` is a linear map
into `SheafHom(A^m, j_!M^{n+m})`, and *that* the adjunction does identify. The two routes prove
the same thing; the internal-hom route is the available one, because the internal hom of sheaves
of modules is in the library while the tensor product of sheaves of modules over a sheaf of
graded algebras is not.

**Where the content of the tag sits.** Both directions of `gradedExtendHomEquiv` and of
`gradedHomOfDegreeExtendEquiv` are the degreewise adjunction on underlying sheaves of modules;
what has to be proved is that the bijection matches the `A`-linear maps on one side with the
`A_U`-linear maps on the other, which is exactly what the source says the work is. The forward
direction is a rewrite by `gradedExtendedAction_unit`. The backward direction cannot be, since
`A`-linearity of the adjoint map is an identity of bilinear maps out of `j_!M^n` and the unit
sections are not all the sections; it is proved by
`SheafOfModules.extendedBilinear_ext`, which reduces such an identity to its values on the unit
sections.

The degrees of a `GradedHomOfDegree` are carried as an index `j` together with a proof
`i + n = j`, so the two sides of each `map_mul` obligation below live in the same homogeneous
piece and no `HEq` occurs in the adjunction. `HEq` is unavoidable in the associativity and unit
laws of the action itself, whose two sides are indexed by `(n + i) + j` and `n + (i + j)`; those
are proved by the trilinear, respectively linear, extensionality principle of the bilinear file.

**Base.** The ringed site is unbundled as a sheaf of commutative rings `O` on an arbitrary site,
with `Stacks.SheafOfModules.Tensor.ringSheaf O` the sheaf of rings that sheaves of modules are
taken over. The commutativity of `O` is used only through the internal hom, which Tag 03EM states
for a presheaf of commutative rings. The universes of the site, of the ring and of the module
sections stay independent, except that the module universe is `max u v m`, which is forced by the
extension-by-zero adjunction.

## References

* [Stacks Project, Tag 0FRA](https://stacks.math.columbia.edu/tag/0FRA)
* [Stacks Project, Tag 0FR1](https://stacks.math.columbia.edu/tag/0FR1)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
-/

@[expose] public section

open CategoryTheory Opposite

universe m w v u

namespace SheafOfModules

/-! ### Generic auxiliaries -/

section Generic

universe t a m₁ v₁ u₁

variable {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{t}}

/-- The right action of a right graded module, read as a bilinear map of sheaves of modules.
This is a repackaging of the `smul` field and its three laws, not a new datum. -/
def GradedModule.actionBilinear {B : GradedAlgebra.{t, a} R}
    (M : GradedModule.{t, a, m₁} B) (n i : ℤ) :
    BilinearMap (M.piece n) (B.piece i) (M.piece (n + i)) where
  app := M.smul n i
  map_smul_left := M.smul_smul_left n i
  map_smul_right := M.smul_smul_right n i
  naturality := M.smul_naturality n i

/-- The components of `M.actionBilinear n i` are the action maps `M.smul n i`. -/
@[simp]
theorem GradedModule.actionBilinear_app {B : GradedAlgebra.{t, a} R}
    (M : GradedModule.{t, a, m₁} B) (n i : ℤ) (V : Dᵒᵖ) :
    (M.actionBilinear n i).app V = M.smul n i V := rfl

/-- A family of morphisms of sheaves of modules indexed by `ℤ`, applied to two heterogeneously
equal sections of differently indexed members, gives heterogeneously equal results. This is the
transport that lets a law whose two sides are indexed by `(n + i) + j` and `n + (i + j)` be
rewritten. -/
theorem heq_family_app {P Q : ℤ → SheafOfModules.{m₁} R} (φ : ∀ k, P k ⟶ Q k) (V : Dᵒᵖ)
    {k l : ℤ} (hkl : k = l) {x : (P k).val.obj V} {y : (P l).val.obj V} (hxy : HEq x y) :
    HEq ((φ k).val.app V x) ((φ l).val.app V y) := by
  subst hkl
  rw [eq_of_heq hxy]

/-! ### Composing homogeneous homomorphisms -/

variable {B : GradedAlgebra.{t, a} R} {M N P : GradedModule.{t, a, m₁} B}

/-- Precomposition of a homogeneous homomorphism of degree `n` with a homomorphism of graded
modules. -/
def GradedHomOfDegree.compLeft (g : M ⟶ N) {n : ℤ} (f : GradedHomOfDegree N P n) :
    GradedHomOfDegree M P n where
  app i j hij := g.app i ≫ f.app i j hij
  map_mul i j hij p V x b := by
    change (f.app (i + p) (j + p) (by omega)).val.app V
      ((g.app (i + p)).val.app V (M.smul i p V x b)) = _
    rw [g.map_smul, f.map_mul]
    rfl

/-- Postcomposition of a homogeneous homomorphism of degree `n` with a homomorphism of graded
modules. -/
def GradedHomOfDegree.compRight {n : ℤ} (f : GradedHomOfDegree M N n) (k : N ⟶ P) :
    GradedHomOfDegree M P n where
  app i j hij := f.app i j hij ≫ k.app j
  map_mul i j hij p V x b := by
    change (k.app (j + p)).val.app V
      ((f.app (i + p) (j + p) (by omega)).val.app V (M.smul i p V x b)) = _
    rw [f.map_mul, k.map_smul]
    rfl

/-- The components of `GradedHomOfDegree.compLeft g f` are the composites
`g.app i ≫ f.app i j hij`. -/
@[simp]
theorem GradedHomOfDegree.compLeft_app (g : M ⟶ N) {n : ℤ} (f : GradedHomOfDegree N P n)
    (i j : ℤ) (hij : i + n = j) :
    (GradedHomOfDegree.compLeft g f).app i j hij = g.app i ≫ f.app i j hij := rfl

/-- The components of `f.compRight k` are the composites `f.app i j hij ≫ k.app j`. -/
@[simp]
theorem GradedHomOfDegree.compRight_app {n : ℤ} (f : GradedHomOfDegree M N n) (k : N ⟶ P)
    (i j : ℤ) (hij : i + n = j) :
    (f.compRight k).app i j hij = f.app i j hij ≫ k.app j := rfl

end Generic

/-! ### The extended action -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}]
  (O : Sheaf J CommRingCat.{w}) (U : C)

variable (A : GradedAlgebra.{w, max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))

/-- `j_{U!}` on ordinary sheaves of modules over the structure sheaf of the ringed site. -/
@[sga "2 VI 1.4" "Z open"]
noncomputable abbrev extendSheaf :
    SheafOfModules.{max u v m} (((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).over U) ⥤
      SheafOfModules.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) :=
  extensionByZero.{m, w, v, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U

/-- The adjunction `j_{U!} ⊣ j_U^*` on ordinary sheaves of modules. -/
noncomputable abbrev extendSheafAdjunction :
    extendSheaf.{m} O U ⊣
      overFunctor.{max u v m} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U :=
  extensionByZeroAdjunction.{m, w, v, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) U

/-- **The right `A`-action on the degreewise extension by zero of a right graded `A_U`-module.**
It is the action of `M` transported across the adjunction by
`SheafOfModules.extendBilinear`; `SheafOfModules.gradedExtendedAction_unit` says that it agrees
with the action of `M` on the sections supplied by the unit, and that is all any consumer
needs. -/
noncomputable def gradedExtendedAction
    (M : GradedModule.{w, max u v m, max u v m} (A.over U)) (n i : ℤ) :
    BilinearMap ((extendSheaf.{m} O U).obj (M.piece n)) (A.piece i)
      ((extendSheaf.{m} O U).obj (M.piece (n + i))) :=
  extendBilinear.{m, w, v, u} O U
    (bilinearPostcomp
      (M.actionBilinear n i : BilinearMap (M.piece n) ((A.piece i).over U) (M.piece (n + i)))
      ((extendSheafAdjunction.{m} O U).unit.app (M.piece (n + i))))

/-- **The extended action on the sections supplied by the unit.** This is the defining property
of `SheafOfModules.gradedExtendedAction`. -/
theorem gradedExtendedAction_unit
    (M : GradedModule.{w, max u v m, max u v m} (A.over U)) (n i : ℤ)
    (V : (Over U)ᵒᵖ) (x : (M.piece n).val.obj V)
    (a : (A.piece i).val.obj (op V.unop.left)) :
    (gradedExtendedAction.{m} O U A M n i).app (op V.unop.left)
        (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app V x) a =
      ((extendSheafAdjunction.{m} O U).unit.app (M.piece (n + i))).val.app V
        (M.smul n i V x a) :=
  extendBilinear_unit.{m, w, v, u} O U _ V x a

/-- The extended action commutes with the extension by zero of a homomorphism of graded
modules. -/
theorem gradedExtendedAction_map
    {M N : GradedModule.{w, max u v m, max u v m} (A.over U)} (f : M ⟶ N) (n i : ℤ)
    (V : Cᵒᵖ) (x : ((extendSheaf.{m} O U).obj (M.piece n)).val.obj V)
    (a : (A.piece i).val.obj V) :
    ((extendSheaf.{m} O U).map (f.app (n + i))).val.app V
        ((gradedExtendedAction.{m} O U A M n i).app V x a) =
      (gradedExtendedAction.{m} O U A N n i).app V
        (((extendSheaf.{m} O U).map (f.app n)).val.app V x) a := by
  refine extendedBilinear_ext.{m, w, v, u} O U
    (bilinearPostcomp (gradedExtendedAction.{m} O U A M n i)
      ((extendSheaf.{m} O U).map (f.app (n + i))))
    (Stacks.BilinearMap.compLeft (gradedExtendedAction.{m} O U A N n i)
      ((extendSheaf.{m} O U).map (f.app n)).val) ?_ V x a
  intro W z b
  have hn (k : ℤ) (y : (M.piece k).val.obj W) :
      ((extendSheaf.{m} O U).map (f.app k)).val.app (op W.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.piece k)).val.app W y) =
        ((extendSheafAdjunction.{m} O U).unit.app (N.piece k)).val.app W
          ((f.app k).val.app W y) :=
    congrArg (fun s => s.val.app W y)
      ((extendSheafAdjunction.{m} O U).unit.naturality (f.app k)).symm
  show ((extendSheaf.{m} O U).map (f.app (n + i))).val.app (op W.unop.left)
      ((gradedExtendedAction.{m} O U A M n i).app (op W.unop.left)
        (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app W z) b) =
    (gradedExtendedAction.{m} O U A N n i).app (op W.unop.left)
      (((extendSheaf.{m} O U).map (f.app n)).val.app (op W.unop.left)
        (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app W z)) b
  rw [gradedExtendedAction_unit, hn, hn, gradedExtendedAction_unit]
  exact congrArg
    (((extendSheafAdjunction.{m} O U).unit.app (N.piece (n + i))).val.app W)
    (f.map_smul n i W z b)

/-- The degree-zero unit of `A` acts as the identity on the extension by zero. -/
theorem gradedExtendedAction_one
    (M : GradedModule.{w, max u v m, max u v m} (A.over U)) (n : ℤ)
    (V : Cᵒᵖ) (x : ((extendSheaf.{m} O U).obj (M.piece n)).val.obj V) :
    HEq ((gradedExtendedAction.{m} O U A M n 0).app V x (A.one.eval V)) x := by
  refine extendedHom_hext.{m, w, v, u} O U
    (congrArg (fun k => (extendSheaf.{m} O U).obj (M.piece k)) (add_zero n))
    (bilinearApplySection (gradedExtendedAction.{m} O U A M n 0) A.one) (𝟙 _) ?_ V x
  intro W y
  show HEq ((gradedExtendedAction.{m} O U A M n 0).app (op W.unop.left)
    (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app W y)
    (A.one.eval (op W.unop.left))) _
  rw [gradedExtendedAction_unit]
  exact heq_family_app
    (fun k => (extendSheafAdjunction.{m} O U).unit.app (M.piece k)) W (add_zero n)
    (M.smul_one n W y)

/-- The extended action is associative. -/
theorem gradedExtendedAction_assoc
    (M : GradedModule.{w, max u v m, max u v m} (A.over U)) (n i j : ℤ)
    (V : Cᵒᵖ) (x : ((extendSheaf.{m} O U).obj (M.piece n)).val.obj V)
    (a : (A.piece i).val.obj V) (b : (A.piece j).val.obj V) :
    HEq ((gradedExtendedAction.{m} O U A M (n + i) j).app V
        ((gradedExtendedAction.{m} O U A M n i).app V x a) b)
      ((gradedExtendedAction.{m} O U A M n (i + j)).app V x ((A.mul i j).app V a b)) := by
  refine extendedTrilinear_hext.{m, w, v, u} O U
    (congrArg (fun k => (extendSheaf.{m} O U).obj (M.piece k)) (add_assoc n i j))
    (trilinearCompLeft (gradedExtendedAction.{m} O U A M n i)
      (gradedExtendedAction.{m} O U A M (n + i) j))
    (trilinearCompRight (gradedExtendedAction.{m} O U A M n (i + j))
      (A.mul i j)) ?_ V x a b
  intro W y c d
  show HEq ((gradedExtendedAction.{m} O U A M (n + i) j).app (op W.unop.left)
      ((gradedExtendedAction.{m} O U A M n i).app (op W.unop.left)
        (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app W y) c) d)
    ((gradedExtendedAction.{m} O U A M n (i + j)).app (op W.unop.left)
      (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app W y)
      ((A.mul i j).app (op W.unop.left) c d))
  rw [gradedExtendedAction_unit, gradedExtendedAction_unit, gradedExtendedAction_unit]
  exact heq_family_app
    (fun k => (extendSheafAdjunction.{m} O U).unit.app (M.piece k)) W (add_assoc n i j)
    (M.smul_mul n i j W y c d)

/-! ### The functor `j_!` on graded modules -/

/-- **`j_!M`, the extension by zero of a right graded `A_U`-module.** Its homogeneous pieces are
the extensions by zero `j_!M^n` of those of `M`, and its action is
`SheafOfModules.gradedExtendedAction`. -/
noncomputable def gradedExtensionByZero
    (M : GradedModule.{w, max u v m, max u v m} (A.over U)) :
    GradedModule.{w, max u v m, max u v m} A where
  piece n := (extendSheaf.{m} O U).obj (M.piece n)
  smul n i := (gradedExtendedAction.{m} O U A M n i).app
  smul_smul_left n i := (gradedExtendedAction.{m} O U A M n i).map_smul_left
  smul_smul_right n i := (gradedExtendedAction.{m} O U A M n i).map_smul_right
  smul_naturality n i := (gradedExtendedAction.{m} O U A M n i).naturality
  smul_mul := gradedExtendedAction_assoc.{m} O U A M
  smul_one := gradedExtendedAction_one.{m} O U A M

/-- The homogeneous piece of degree `n` of `j_!M` is the extension by zero `j_!(M^n)`. -/
@[simp]
theorem gradedExtensionByZero_piece
    (M : GradedModule.{w, max u v m, max u v m} (A.over U)) (n : ℤ) :
    (gradedExtensionByZero.{m} O U A M).piece n = (extendSheaf.{m} O U).obj (M.piece n) := rfl

/-- The action of `A` on `j_!M` is `SheafOfModules.gradedExtendedAction`. -/
@[simp]
theorem gradedExtensionByZero_smul
    (M : GradedModule.{w, max u v m, max u v m} (A.over U)) (n i : ℤ) (V : Cᵒᵖ) :
    (gradedExtensionByZero.{m} O U A M).smul n i V =
      (gradedExtendedAction.{m} O U A M n i).app V := rfl

/-- The extension by zero of a homomorphism of right graded `A_U`-modules. -/
noncomputable def gradedExtensionByZeroMap
    {M N : GradedModule.{w, max u v m, max u v m} (A.over U)} (f : M ⟶ N) :
    gradedExtensionByZero.{m} O U A M ⟶ gradedExtensionByZero.{m} O U A N where
  app n := (extendSheaf.{m} O U).map (f.app n)
  map_smul := gradedExtendedAction_map.{m} O U A f

/-- **The functor `j_! : Mod^gr(A_U) ⥤ Mod^gr(A)`.** -/
noncomputable def gradedExtensionByZeroFunctor :
    GradedModule.{w, max u v m, max u v m} (A.over U) ⥤
      GradedModule.{w, max u v m, max u v m} A where
  obj M := gradedExtensionByZero.{m} O U A M
  map f := gradedExtensionByZeroMap.{m} O U A f
  map_id M := GradedModule.Hom.ext fun n => (extendSheaf.{m} O U).map_id (M.piece n)
  map_comp f g := GradedModule.Hom.ext fun n =>
    (extendSheaf.{m} O U).map_comp (f.app n) (g.app n)

/-- The functor `j_!` sends `M` to `SheafOfModules.gradedExtensionByZero`. -/
@[simp]
theorem gradedExtensionByZeroFunctor_obj
    (M : GradedModule.{w, max u v m, max u v m} (A.over U)) :
    (gradedExtensionByZeroFunctor.{m} O U A).obj M = gradedExtensionByZero.{m} O U A M := rfl

/-- In degree `n`, the functor `j_!` sends a homomorphism `f` to the extension by zero of
`f.app n`. -/
@[simp]
theorem gradedExtensionByZeroFunctor_map_app
    {M N : GradedModule.{w, max u v m, max u v m} (A.over U)} (f : M ⟶ N) (n : ℤ) :
    ((gradedExtensionByZeroFunctor.{m} O U A).map f).app n =
      (extendSheaf.{m} O U).map (f.app n) := rfl

/-! ### The adjunction `j_! ⊣ j^*`: Tag 0FRA -/

/-- The homomorphism `M ⟶ j^*N` of right graded `A_U`-modules adjoint to a homomorphism
`j_!M ⟶ N` of right graded `A`-modules. -/
noncomputable def gradedExtendAdjoint
    (M : GradedModule.{w, max u v m, max u v m} (A.over U))
    (N : GradedModule.{w, max u v m, max u v m} A)
    (f : gradedExtensionByZero.{m} O U A M ⟶ N) : M ⟶ N.over U where
  app n := (extendSheafAdjunction.{m} O U).homEquiv (M.piece n) (N.piece n) (f.app n)
  map_smul n i V x b := by
    change (f.app (n + i)).val.app (op V.unop.left)
        (((extendSheafAdjunction.{m} O U).unit.app (M.piece (n + i))).val.app V
          (M.smul n i V x b)) =
      N.smul n i (op V.unop.left)
        ((f.app n).val.app (op V.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app V x)) b
    rw [← gradedExtendedAction_unit O U A M n i V x b]
    exact f.map_smul n i (op V.unop.left) _ b

/-- The homomorphism `j_!M ⟶ N` of right graded `A`-modules adjoint to a homomorphism
`M ⟶ j^*N` of right graded `A_U`-modules. This is the direction where `A`-linearity has to be
recovered from `A_U`-linearity, which the unit sections alone do not give; the input is
`SheafOfModules.extendedBilinear_ext`. -/
noncomputable def gradedExtendAdjointInv
    (M : GradedModule.{w, max u v m, max u v m} (A.over U))
    (N : GradedModule.{w, max u v m, max u v m} A)
    (f : M ⟶ N.over U) : gradedExtensionByZero.{m} O U A M ⟶ N where
  app n := ((extendSheafAdjunction.{m} O U).homEquiv (M.piece n) (N.piece n)).symm (f.app n)
  map_smul n i V x b := by
    refine extendedBilinear_ext.{m, w, v, u} O U
      (bilinearPostcomp (gradedExtendedAction.{m} O U A M n i)
        (((extendSheafAdjunction.{m} O U).homEquiv (M.piece (n + i))
          (N.piece (n + i))).symm (f.app (n + i))))
      (Stacks.BilinearMap.compLeft (N.actionBilinear n i)
        (((extendSheafAdjunction.{m} O U).homEquiv (M.piece n) (N.piece n)).symm
          (f.app n)).val) ?_ V x b
    intro W y c
    have hunit (k : ℤ) (z : (M.piece k).val.obj W) :
        ((((extendSheafAdjunction.{m} O U).homEquiv (M.piece k) (N.piece k)).symm
              (f.app k)).val.app (op W.unop.left)
            (((extendSheafAdjunction.{m} O U).unit.app (M.piece k)).val.app W z)) =
          (f.app k).val.app W z :=
      congrArg (fun s => s.val.app W z)
        (((extendSheafAdjunction.{m} O U).homEquiv (M.piece k) (N.piece k)).apply_symm_apply
          (f.app k))
    change ((((extendSheafAdjunction.{m} O U).homEquiv (M.piece (n + i))
          (N.piece (n + i))).symm (f.app (n + i))).val.app (op W.unop.left)
        ((gradedExtendedAction.{m} O U A M n i).app (op W.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app W y) c)) =
      N.smul n i (op W.unop.left)
        ((((extendSheafAdjunction.{m} O U).homEquiv (M.piece n) (N.piece n)).symm
            (f.app n)).val.app (op W.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.piece n)).val.app W y)) c
    rw [gradedExtendedAction_unit, hunit, hunit]
    exact f.map_smul n i W y c

/-- **Tag 0FRA.** The homomorphisms `j_!M ⟶ N` of right graded `A`-modules are the
homomorphisms `M ⟶ j^*N` of right graded `A_U`-modules. The bijection is the degreewise
adjunction `j_{U!} ⊣ j_U^*` of ordinary sheaves of modules; the content is that it matches the
`A`-linear maps with the `A_U`-linear maps. -/
@[stacks 0FRA "Hom(j_! M, N) = Hom(M, j^* N)"]
noncomputable def gradedExtendHomEquiv
    (M : GradedModule.{w, max u v m, max u v m} (A.over U))
    (N : GradedModule.{w, max u v m, max u v m} A) :
    (gradedExtensionByZero.{m} O U A M ⟶ N) ≃ (M ⟶ N.over U) where
  toFun f := gradedExtendAdjoint.{m} O U A M N f
  invFun f := gradedExtendAdjointInv.{m} O U A M N f
  left_inv f := GradedModule.Hom.ext fun n =>
    ((extendSheafAdjunction.{m} O U).homEquiv (M.piece n) (N.piece n)).symm_apply_apply
      (f.app n)
  right_inv f := GradedModule.Hom.ext fun n =>
    ((extendSheafAdjunction.{m} O U).homEquiv (M.piece n) (N.piece n)).apply_symm_apply
      (f.app n)

/-- In degree `n`, `gradedExtendHomEquiv` is the adjunction bijection `j_{U!} ⊣ j_U^*` applied to
`f.app n`. -/
@[simp]
theorem gradedExtendHomEquiv_app
    (M : GradedModule.{w, max u v m, max u v m} (A.over U))
    (N : GradedModule.{w, max u v m, max u v m} A)
    (f : gradedExtensionByZero.{m} O U A M ⟶ N) (n : ℤ) :
    (gradedExtendHomEquiv.{m} O U A M N f).app n =
      (extendSheafAdjunction.{m} O U).homEquiv (M.piece n) (N.piece n) (f.app n) := rfl

/-- **Tag 0FRA, as an adjunction.** `j_! : Mod^gr(A_U) ⥤ Mod^gr(A)` is left adjoint to
`j^* : Mod^gr(A) ⥤ Mod^gr(A_U)`. -/
@[stacks 0FRA "the identification is an adjunction `j_! ⊣ j^*` of graded modules"]
noncomputable def gradedExtensionByZeroAdjunction :
    gradedExtensionByZeroFunctor.{m} O U A ⊣ GradedModule.overFunctor A U :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N := gradedExtendHomEquiv.{m} O U A M N
      homEquiv_naturality_left_symm g f := GradedModule.Hom.ext fun n =>
        (extendSheafAdjunction.{m} O U).homEquiv_naturality_left_symm (g.app n) (f.app n)
      homEquiv_naturality_right f k := GradedModule.Hom.ext fun n =>
        (extendSheafAdjunction.{m} O U).homEquiv_naturality_right (f.app n) (k.app n) }

/-! ### The graded-category refinement of Tag 0FRA -/

variable {M : GradedModule.{w, max u v m, max u v m} (A.over U)}
  {N : GradedModule.{w, max u v m, max u v m} A}

/-- The homogeneous homomorphism `M ⟶ j^*N` of degree `d` adjoint to a homogeneous
homomorphism `j_!M ⟶ N` of degree `d`. -/
noncomputable def gradedHomOfDegreeAdjoint {d : ℤ}
    (f : GradedHomOfDegree (gradedExtensionByZero.{m} O U A M) N d) :
    GradedHomOfDegree M (N.over U) d where
  app i j hij := (extendSheafAdjunction.{m} O U).homEquiv (M.piece i) (N.piece j) (f.app i j hij)
  map_mul i j hij p V x b := by
    change (f.app (i + p) (j + p) (by omega)).val.app (op V.unop.left)
        (((extendSheafAdjunction.{m} O U).unit.app (M.piece (i + p))).val.app V
          (M.smul i p V x b)) =
      N.smul j p (op V.unop.left)
        ((f.app i j hij).val.app (op V.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.piece i)).val.app V x)) b
    rw [← gradedExtendedAction_unit O U A M i p V x b]
    exact f.map_mul i j hij p (op V.unop.left) _ b

/-- The homogeneous homomorphism `j_!M ⟶ N` of degree `d` adjoint to a homogeneous
homomorphism `M ⟶ j^*N` of degree `d`. This is the direction where `A`-linearity has to be
recovered from `A_U`-linearity, which the unit sections alone do not give; the input is
`SheafOfModules.extendedBilinear_ext`. -/
noncomputable def gradedHomOfDegreeAdjointInv {d : ℤ}
    (f : GradedHomOfDegree M (N.over U) d) :
    GradedHomOfDegree (gradedExtensionByZero.{m} O U A M) N d where
  app i j hij :=
    ((extendSheafAdjunction.{m} O U).homEquiv (M.piece i) (N.piece j)).symm (f.app i j hij)
  map_mul i j hij p V x b := by
    refine extendedBilinear_ext.{m, w, v, u} O U
      (bilinearPostcomp (gradedExtendedAction.{m} O U A M i p)
        (((extendSheafAdjunction.{m} O U).homEquiv (M.piece (i + p))
          (N.piece (j + p))).symm (f.app (i + p) (j + p) (by omega))))
      (Stacks.BilinearMap.compLeft (N.actionBilinear j p)
        (((extendSheafAdjunction.{m} O U).homEquiv (M.piece i) (N.piece j)).symm
          (f.app i j hij)).val) ?_ V x b
    intro W y c
    have hunit (k l : ℤ) (hkl : k + d = l) (z : (M.piece k).val.obj W) :
        ((((extendSheafAdjunction.{m} O U).homEquiv (M.piece k) (N.piece l)).symm
              (f.app k l hkl)).val.app (op W.unop.left)
            (((extendSheafAdjunction.{m} O U).unit.app (M.piece k)).val.app W z)) =
          (f.app k l hkl).val.app W z :=
      congrArg (fun s => s.val.app W z)
        (((extendSheafAdjunction.{m} O U).homEquiv (M.piece k) (N.piece l)).apply_symm_apply
          (f.app k l hkl))
    change ((((extendSheafAdjunction.{m} O U).homEquiv (M.piece (i + p))
          (N.piece (j + p))).symm (f.app (i + p) (j + p) (by omega))).val.app (op W.unop.left)
        ((gradedExtendedAction.{m} O U A M i p).app (op W.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.piece i)).val.app W y) c)) =
      N.smul j p (op W.unop.left)
        ((((extendSheafAdjunction.{m} O U).homEquiv (M.piece i) (N.piece j)).symm
            (f.app i j hij)).val.app (op W.unop.left)
          (((extendSheafAdjunction.{m} O U).unit.app (M.piece i)).val.app W y)) c
    rw [gradedExtendedAction_unit, hunit, hunit]
    exact f.map_mul i j hij p W y c

/-- **Tag 0FRA.** In every degree `d` the homogeneous homomorphisms `j_!M ⟶ N` of right graded
`A`-modules are the homogeneous homomorphisms `M ⟶ j^*N` of right graded `A_U`-modules. The
bijection is the degreewise adjunction `j_{U!} ⊣ j_U^*` of ordinary sheaves of modules; the
content is that it matches the `A`-linear maps with the `A_U`-linear maps. In degree `0`, read
together with the naturality below, this is the adjunction `j_! ⊣ j^*` of the source. -/
@[stacks 0FRA "Hom(j_! M, N) = Hom(M, j^* N), in each degree"]
noncomputable def gradedHomOfDegreeExtendEquiv (d : ℤ) :
    GradedHomOfDegree (gradedExtensionByZero.{m} O U A M) N d ≃
      GradedHomOfDegree M (N.over U) d where
  toFun f := gradedHomOfDegreeAdjoint.{m} O U A f
  invFun f := gradedHomOfDegreeAdjointInv.{m} O U A f
  left_inv f := GradedHomOfDegree.ext fun i j hij =>
    ((extendSheafAdjunction.{m} O U).homEquiv (M.piece i) (N.piece j)).symm_apply_apply
      (f.app i j hij)
  right_inv f := GradedHomOfDegree.ext fun i j hij =>
    ((extendSheafAdjunction.{m} O U).homEquiv (M.piece i) (N.piece j)).apply_symm_apply
      (f.app i j hij)

/-- In each pair of degrees `i + d = j`, `gradedHomOfDegreeExtendEquiv` is the adjunction
bijection `j_{U!} ⊣ j_U^*` applied to `f.app i j hij`. -/
@[simp]
theorem gradedHomOfDegreeExtendEquiv_app (d : ℤ)
    (f : GradedHomOfDegree (gradedExtensionByZero.{m} O U A M) N d) (i j : ℤ)
    (hij : i + d = j) :
    (gradedHomOfDegreeExtendEquiv.{m} O U A d f).app i j hij =
      (extendSheafAdjunction.{m} O U).homEquiv (M.piece i) (N.piece j) (f.app i j hij) := rfl

/-- **Tag 0FRA, naturality in the source.** -/
@[stacks 0FRA "naturality of Hom(j_! M, N) = Hom(M, j^* N) in M"]
theorem gradedHomOfDegreeExtendEquiv_naturality_left
    {M' : GradedModule.{w, max u v m, max u v m} (A.over U)} (g : M' ⟶ M) (d : ℤ)
    (f : GradedHomOfDegree (gradedExtensionByZero.{m} O U A M) N d) :
    gradedHomOfDegreeExtendEquiv.{m} O U A d
        (GradedHomOfDegree.compLeft (gradedExtensionByZeroMap.{m} O U A g) f) =
      GradedHomOfDegree.compLeft g (gradedHomOfDegreeExtendEquiv.{m} O U A d f) :=
  GradedHomOfDegree.ext fun i _ hij =>
    (extendSheafAdjunction.{m} O U).homEquiv_naturality_left (g.app i) (f.app i _ hij)

/-- **Tag 0FRA, naturality in the target.** -/
@[stacks 0FRA "naturality of Hom(j_! M, N) = Hom(M, j^* N) in N"]
theorem gradedHomOfDegreeExtendEquiv_naturality_right
    {N' : GradedModule.{w, max u v m, max u v m} A} (k : N ⟶ N') (d : ℤ)
    (f : GradedHomOfDegree (gradedExtensionByZero.{m} O U A M) N d) :
    gradedHomOfDegreeExtendEquiv.{m} O U A d (f.compRight k) =
      (gradedHomOfDegreeExtendEquiv.{m} O U A d f).compRight
        (GradedModule.overMap k U) :=
  GradedHomOfDegree.ext fun i j hij =>
    (extendSheafAdjunction.{m} O U).homEquiv_naturality_right (f.app i j hij) (k.app j)

end SheafOfModules

end
