module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsReflectsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.SmallRepresentatives

/-!
# Differential graded modules over an algebra concentrated in degree zero

Let `C` be a category with the chaotic topology, `R` a sheaf of rings on it and `(A, d)` a sheaf of
differential graded `R`-algebras which is *concentrated in degree zero*: its pieces `A^n` vanish
for `n ≠ 0`, and its degree-zero piece is identified with a presheaf of commutative rings `O`.
A right differential graded `A`-module is then the same thing as a cochain complex of
`O`-modules: the right action of `A^0 = O` on each piece `M^n` is a module structure, the
differential is `O`-linear because `d` vanishes on `A^0` (its target `A^1` is zero), and the
structure of `R`-module is recovered from the `O`-module structure along `r ↦ r · 1`.

This is the identification `Mod(O, 0) = Comp(O)` of the Stacks project, Section 24.33
(Tag 0GZ8), used implicitly when the quasi-coherent objects of Cohomology on Sites, Definition
0GYV are compared with those of Differential Graded Sheaves, Definition 0GZ9.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.DegreeZero.Data`: an identification of `A` with `O`
  placed in degree zero.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.toComplex`: a right differential graded
  `A`-module read as a cochain complex of presheaves of `O`-modules.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.ofComplex`: the inverse construction.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.equivalence`: the equivalence
  `Mod(A, d) ≌ CochainComplex (PresheafOfModules O) ℤ`.

## Main results

* `SheafOfModules.DifferentialGradedModule.DegreeZero.quasiIso_toComplexMap_iff`: a homomorphism
  of right differential graded `A`-modules is a quasi-isomorphism of the underlying complexes of
  `R`-modules exactly when it is one of the complexes of `O`-modules.
* `SheafOfModules.DifferentialGradedModule.DegreeZero.homotopyToComplex`: a homotopy of
  homomorphisms of right differential graded `A`-modules is a homotopy of the complexes of
  `O`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory

universe a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

namespace DegreeZero

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{a}}

/-- **An identification of a sheaf of differential graded algebras with a presheaf of commutative
rings placed in degree zero.** The pieces of `A` in nonzero degrees vanish, and the degree-zero
piece is identified, compatibly with multiplication, unit and restriction, with `O`. -/
structure Data (A : DifferentialGradedAlgebra.{a, a} R) (O : Cᵒᵖ ⥤ RingCat.{a}) where
  /-- The identification of the sections of `O` with the degree-zero sections of `A`. -/
  ψ (U : Cᵒᵖ) : O.obj U ≃+ (A.complex.X 0).val.obj U
  /-- `ψ` carries multiplication in `O` to the multiplication of `A` in degrees `0, 0`. -/
  ψ_mul (U : Cᵒᵖ) (x y : O.obj U) : ψ U (x * y) = (A.mul 0 0).app U (ψ U x) (ψ U y)
  /-- `ψ` carries the unit of `O` to the unit of `A`. -/
  ψ_one (U : Cᵒᵖ) : ψ U 1 = A.one.eval U
  /-- `ψ` commutes with the restriction maps. -/
  ψ_map {U V : Cᵒᵖ} (f : U ⟶ V) (x : O.obj U) :
    ψ V (O.map f x) = (A.complex.X 0).val.map f (ψ U x)
  /-- The pieces of `A` in nonzero degrees have at most one section over each object. -/
  subsingleton (n : ℤ) (hn : n ≠ 0) (U : Cᵒᵖ) : Subsingleton ((A.complex.X n).val.obj U)
  /-- The rings of sections of `O` are commutative. -/
  comm (U : Cᵒᵖ) (x y : O.obj U) : x * y = y * x

variable {A : DifferentialGradedAlgebra.{a, a} R} {O : Cᵒᵖ ⥤ RingCat.{a}} (D : Data A O)

/-! ### Transport along equalities of degrees -/

section Cast

variable (M : DifferentialGradedModule.{a, a, m} A) (U : Cᵒᵖ)

/-- The sections over `U` of the degree-`n` piece of a differential graded module. -/
abbrev piece (n : ℤ) : Type m := (M.complex.X n).val.obj U

variable {M U}

/-- Transport along `n = n` is the identity. -/
theorem gradedCast_self {n : ℤ} (h : n = n) (x : piece M U n) :
    gradedCast (piece M U) h x = x := rfl

/-- Transport along `i = j` followed by transport along `j = k` is transport along `i = k`. -/
theorem gradedCast_cast {i j k : ℤ} (h : i = j) (h' : j = k) (x : piece M U i) :
    gradedCast (piece M U) h' (gradedCast (piece M U) h x) =
      gradedCast (piece M U) (h.trans h') x :=
  gradedCast_trans _ h h' x

/-- The transport of `x` along `i = j` equals `y` if and only if `x` and `y` are heterogeneously
equal. -/
theorem gradedCast_eq_iff_heq {i j : ℤ} (h : i = j) (x : piece M U i) (y : piece M U j) :
    gradedCast (piece M U) h x = y ↔ x ≍ y := by
  subst h
  exact ⟨fun h => heq_of_eq h, fun h => eq_of_heq h⟩

/-- The right action of `A` on a section transported along `p = q` agrees, up to heterogeneous
equality, with its action on the original section. -/
theorem mul_gradedCast_heq {p q : ℤ} (h : p = q) (j : ℤ) (y : piece M U p)
    (z : (A.complex.X j).val.obj U) :
    (M.mul q j).app U (gradedCast (piece M U) h y) z ≍ (M.mul p j).app U y z := by
  subst h
  rfl

/-- The differential of `M` commutes with transport along `p = q`. -/
theorem d_gradedCast {p q : ℤ} (h : p = q) (y : piece M U p) :
    (M.complex.d q (q + 1)).val.app U (gradedCast (piece M U) h y) =
      gradedCast (piece M U) (congrArg (· + 1) h) ((M.complex.d p (p + 1)).val.app U y) := by
  subst h
  rfl

/-- The restriction maps of `M` commute with transport along `p = q`. -/
theorem map_gradedCast {V : Cᵒᵖ} (f : U ⟶ V) {p q : ℤ} (h : p = q) (y : piece M U p) :
    (M.complex.X q).val.map f (gradedCast (piece M U) h y) =
      gradedCast (piece M V) h ((M.complex.X p).val.map f y) := by
  subst h
  rfl

/-- Transport along `i = j` is additive. -/
theorem gradedCast_add' {i j : ℤ} (h : i = j) (x y : piece M U i) :
    gradedCast (piece M U) h (x + y) =
      gradedCast (piece M U) h x + gradedCast (piece M U) h y :=
  gradedCast_add _ h x y

/-- Transport along `i = j` sends zero to zero. -/
theorem gradedCast_zero' {i j : ℤ} (h : i = j) :
    gradedCast (piece M U) h (0 : piece M U i) = 0 :=
  gradedCast_zero _ h

end Cast

/-! ### The action of `O` on the pieces of a module -/

section Action

variable (M : DifferentialGradedModule.{a, a, m} A) (U : Cᵒᵖ) (n : ℤ)

/-- The action of a section `b` of `O` on the degree-`n` sections of `M`: the right action of the
corresponding degree-zero section of `A`, read back in degree `n`. -/
def act (b : O.obj U) (x : piece M U n) : piece M U n :=
  gradedCast (piece M U) (add_zero n) ((M.mul n 0).app U x (D.ψ U b))

variable {M U n}

/-- The action of `b` on `x` is heterogeneously equal to the right action of `ψ b` on `x`, which
lies in degree `n + 0`. -/
theorem act_heq (b : O.obj U) (x : piece M U n) :
    act D M U n b x ≍ (M.mul n 0).app U x (D.ψ U b) :=
  ((gradedCast_eq_iff_heq (add_zero n) _ _).1 rfl).symm

/-- The action of a section of `O` is additive in the module section. -/
theorem act_add (b : O.obj U) (x y : piece M U n) :
    act D M U n b (x + y) = act D M U n b x + act D M U n b y := by
  simp only [act, map_add, AddMonoidHom.add_apply, gradedCast_add']

/-- A section of `O` acts on the zero section as zero. -/
theorem act_zero (b : O.obj U) : act D M U n b 0 = 0 := by
  simp only [act, map_zero, AddMonoidHom.zero_apply, gradedCast_zero']

/-- The action is additive in the section of `O`. -/
theorem add_act (b c : O.obj U) (x : piece M U n) :
    act D M U n (b + c) x = act D M U n b x + act D M U n c x := by
  simp only [act, map_add, gradedCast_add']

/-- The zero section of `O` acts as zero. -/
theorem zero_act (x : piece M U n) : act D M U n 0 x = 0 := by
  simp only [act, map_zero, gradedCast_zero']

/-- The unit section of `O` acts as the identity. -/
theorem one_act (x : piece M U n) : act D M U n 1 x = x := by
  rw [act, D.ψ_one, gradedCast_eq_iff_heq]
  exact M.mul_one n U x

/-- Acting by `c` and then by `b` is acting by `c * b`, as for a right action. -/
theorem act_act (b c : O.obj U) (x : piece M U n) :
    act D M U n b (act D M U n c x) = act D M U n (c * b) x := by
  apply eq_of_heq
  refine (act_heq D b _).trans ?_
  refine (mul_gradedCast_heq (add_zero n) 0 _ _).trans ?_
  refine HEq.trans ?_ (act_heq D (c * b) x).symm
  rw [D.ψ_mul]
  exact M.mul_assoc n 0 0 U x (D.ψ U c) (D.ψ U b)

/-- **The degree-`n` sections of `M` form a module over the sections of `O`.** -/
@[implicit_reducible]
def pieceModule : Module (O.obj U) (piece M U n) where
  smul b x := act D M U n b x
  one_smul := one_act D
  mul_smul b c x :=
    (by rw [act_act, D.comm U c b] :
      act D M U n b (act D M U n c x) = act D M U n (b * c) x).symm
  smul_zero := act_zero D
  smul_add := act_add D
  add_smul := add_act D
  zero_smul := zero_act D

end Action

/-! ### A differential graded module as a complex of `O`-modules -/

section AddPresheaf

/-- The presheaf of abelian groups underlying a sheaf of modules, with restriction maps given by
those of the sheaf of modules. -/
def addPresheaf (N : SheafOfModules.{m} R) : Cᵒᵖ ⥤ AddCommGrpCat.{m} where
  obj U := AddCommGrpCat.of (N.val.obj U)
  map f := AddCommGrpCat.ofHom (N.val.map f).hom.toAddMonoidHom
  map_id U := by
    ext x
    exact (PresheafOfModules.congr_map_apply N.val rfl x).trans (by simp; rfl)
  map_comp f g := by
    ext x
    exact N.val.map_comp_apply f g x

/-- The restriction maps of `addPresheaf N` are those of `N`. -/
@[simp]
theorem addPresheaf_map_apply (N : SheafOfModules.{m} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : N.val.obj U) : (addPresheaf N).map f x = N.val.map f x := rfl

/-- A morphism of sheaves of modules, as a morphism of the underlying presheaves of abelian
groups. -/
def addPresheafMap {N N' : SheafOfModules.{m} R} (φ : N ⟶ N') : addPresheaf N ⟶ addPresheaf N' where
  app U := AddCommGrpCat.ofHom (φ.val.app U).hom.toAddMonoidHom
  naturality U V f := by
    ext x
    exact PresheafOfModules.naturality_apply φ.val f x

/-- The components of `addPresheafMap φ` are those of `φ`. -/
@[simp]
theorem addPresheafMap_app_apply {N N' : SheafOfModules.{m} R} (φ : N ⟶ N') (U : Cᵒᵖ)
    (x : N.val.obj U) : (addPresheafMap φ).app U x = φ.val.app U x := rfl

end AddPresheaf

section ToComplex

variable (M : DifferentialGradedModule.{a, a, m} A)

/-- The action of `O` commutes with the restriction maps of `M`. -/
theorem act_map {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℤ) (b : O.obj U) (x : piece M U n) :
    (M.complex.X n).val.map f (act D M U n b x) =
      act D M V n (O.map f b) ((M.complex.X n).val.map f x) := by
  unfold act
  rw [map_gradedCast, D.ψ_map]
  congr 1
  exact (M.mul n 0).naturality f x (D.ψ U b)

/-- Sections of the pieces of `A` in nonzero degrees are zero. -/
private theorem eq_zero_of_ne_zero_deg (D : Data A O) {U : Cᵒᵖ} {n : ℤ} (hn : n ≠ 0)
    (y : (A.complex.X n).val.obj U) : y = 0 :=
  (D.subsingleton n hn U).elim _ _

/-- The differential `d : M^n → M^(n+1)` is linear for the action of `O`. -/
theorem d_act (U : Cᵒᵖ) (n : ℤ) (b : O.obj U) (x : piece M U n) :
    (M.complex.d n (n + 1)).val.app U (act D M U n b x) =
      act D M U (n + 1) b ((M.complex.d n (n + 1)).val.app U x) := by
  have h0 : (A.complex.d 0 (0 + 1)).val.app U (D.ψ U b) = 0 :=
    eq_zero_of_ne_zero_deg D (by omega) _
  have key := M.leibniz n 0 U x (D.ψ U b)
  rw [h0, map_zero, gradedCast_zero', smul_zero,
    add_zero (gradedCast (fun q ↦ ((M.complex.X q).val.obj U : Type m)) _ _)] at key
  unfold act
  rw [d_gradedCast (add_zero n), key, gradedCast_cast]

/-- Every component `d : M^i → M^j` of the differential is linear for the action of `O`. -/
theorem d_act' (U : Cᵒᵖ) (i j : ℤ) (b : O.obj U) (x : piece M U i) :
    (M.complex.d i j).val.app U (act D M U i b x) =
      act D M U j b ((M.complex.d i j).val.app U x) := by
  by_cases h : i + 1 = j
  · subst h
    exact d_act D M U i b x
  · have hd : M.complex.d i j = 0 := M.complex.shape i j h
    rw [hd]
    exact (act_zero D b).symm

include D in
/-- The degree-`n` piece of `M` as a presheaf of `O`-modules. -/
def toPiece (n : ℤ) : PresheafOfModules.{m} O :=
  letI : ∀ U : Cᵒᵖ, Module (O.obj U) ((addPresheaf (M.complex.X n)).obj U) :=
    fun U => pieceModule D (M := M) (U := U) (n := n)
  PresheafOfModules.ofPresheaf (addPresheaf (M.complex.X n))
    (fun _ _ f b x => act_map D M f n b x)

/-- Scalar multiplication on `toPiece D M n` is the action `act`. -/
theorem toPiece_smul (n : ℤ) (U : Cᵒᵖ) (b : O.obj U) (x : (toPiece D M n).obj U) :
    b • x = act D M U n b x := rfl

/-- The differential of `M`, read as a morphism of presheaves of `O`-modules. -/
def toD (i j : ℤ) : toPiece D M i ⟶ toPiece D M j :=
  PresheafOfModules.homMk (addPresheafMap (M.complex.d i j))
    (fun U b x => d_act' D M U i j b x)

/-- The components of `toD D M i j` are those of the differential of `M`. -/
@[simp]
theorem toD_app_apply (i j : ℤ) (U : Cᵒᵖ) (x : (toPiece D M i).obj U) :
    (toD D M i j).app U x = (M.complex.d i j).val.app U x := rfl

/-- **A right differential graded `A`-module, read as a cochain complex of presheaves of
`O`-modules.** -/
def toComplex : CochainComplex (PresheafOfModules.{m} O) ℤ where
  X n := toPiece D M n
  d i j := toD D M i j
  shape i j h := by
    have hd : M.complex.d i j = 0 := M.complex.shape i j h
    ext U x
    exact (toD_app_apply D M i j U x).trans (by rw [hd]; rfl)
  d_comp_d' i j k _ _ := by
    have hd : M.complex.d i j ≫ M.complex.d j k = 0 := M.complex.d_comp_d i j k
    ext U x
    exact (congrArg (fun φ => φ.val.app U x) hd : _)

end ToComplex

section ToComplexMap

variable {M N : DifferentialGradedModule.{a, a, m} A}

/-- A homomorphism of differential graded modules commutes with transport along `p = q`. -/
theorem f_gradedCast (f : M ⟶ N) (U : Cᵒᵖ) {p q : ℤ} (h : p = q) (y : piece M U p) :
    (f.toHomologicalComplex.f q).val.app U (gradedCast (piece M U) h y) =
      gradedCast (piece N U) h ((f.toHomologicalComplex.f p).val.app U y) := by
  subst h
  rfl

/-- A homomorphism of differential graded modules is linear for the action of `O`. -/
theorem f_act (f : M ⟶ N) (U : Cᵒᵖ) (n : ℤ) (b : O.obj U) (x : piece M U n) :
    (f.toHomologicalComplex.f n).val.app U (act D M U n b x) =
      act D N U n b ((f.toHomologicalComplex.f n).val.app U x) := by
  unfold act
  rw [f_gradedCast, f.map_mul]

/-- A homomorphism of right differential graded modules, as a morphism of complexes of
presheaves of `O`-modules. -/
def toComplexMap (f : M ⟶ N) : toComplex D M ⟶ toComplex D N where
  f n := PresheafOfModules.homMk (addPresheafMap (f.toHomologicalComplex.f n))
    (fun U b x => f_act D f U n b x)
  comm' i j _ := by
    have hc := f.toHomologicalComplex.comm i j
    ext U x
    exact (congrArg (fun φ => φ.val.app U x) hc : _)

/-- The components of `toComplexMap D f` are those of `f`. -/
@[simp]
theorem toComplexMap_f_app_apply (f : M ⟶ N) (n : ℤ) (U : Cᵒᵖ)
    (x : (toPiece D M n).obj U) :
    ((toComplexMap D f).f n).app U x = (f.toHomologicalComplex.f n).val.app U x := rfl

end ToComplexMap

/-- **Right differential graded `A`-modules as cochain complexes of presheaves of `O`-modules**,
as a functor. -/
def toComplexFunctor :
    DifferentialGradedModule.{a, a, m} A ⥤ CochainComplex (PresheafOfModules.{m} O) ℤ where
  obj M := toComplex D M
  map f := toComplexMap D f
  map_id M := by
    ext n U x
    rfl
  map_comp f g := by
    ext n U x
    rfl

/-! ### The scalars of `R` inside `O` -/

/-- The ring homomorphism `R(U) ⟶ O(U)`, `r ↦ r · 1`. -/
def scalarRingHom (U : Cᵒᵖ) : R.obj.obj U →+* O.obj U where
  toFun r := (D.ψ U).symm (r • A.one.eval U)
  map_one' := by
    rw [one_smul, ← D.ψ_one, AddEquiv.symm_apply_apply]
  map_mul' r s := by
    apply (D.ψ U).injective
    rw [D.ψ_mul]
    simp only [AddEquiv.apply_symm_apply]
    rw [(A.mul 0 0).map_smul_left, (A.mul 0 0).map_smul_right,
      eq_of_heq (A.mul_one 0 U (A.one.eval U)), mul_smul]
  map_zero' := by
    rw [zero_smul, map_zero]
  map_add' r s := by
    rw [add_smul, map_add]

/-- The image of `r` in `O` corresponds under `ψ` to `r · 1`. -/
theorem ψ_scalarRingHom (U : Cᵒᵖ) (r : R.obj.obj U) :
    D.ψ U (scalarRingHom D U r) = r • A.one.eval U :=
  AddEquiv.apply_symm_apply _ _

/-- The morphism of presheaves of rings `R ⟶ O`, `r ↦ r · 1`. -/
def scalarHom : R.obj ⟶ O where
  app U := RingCat.ofHom (scalarRingHom D U)
  naturality U V f := by
    ext r
    apply (D.ψ V).injective
    change D.ψ V (scalarRingHom D V (R.obj.map f r)) = D.ψ V (O.map f (scalarRingHom D U r))
    rw [ψ_scalarRingHom, D.ψ_map, ψ_scalarRingHom, (A.complex.X 0).val.map_smul,
      PresheafOfModules.sections_property]
    rfl

/-- Multiplication by the image of `r` in `O` corresponds under `ψ` to the scalar action of `r`. -/
theorem ψ_smul (U : Cᵒᵖ) (r : R.obj.obj U) (b : O.obj U) :
    D.ψ U (scalarRingHom D U r * b) = r • D.ψ U b := by
  rw [D.ψ_mul, ψ_scalarRingHom, (A.mul 0 0).map_smul_left]
  congr 1
  exact eq_of_heq (A.one_mul 0 U (D.ψ U b))


/-! ### A complex of `O`-modules as a differential graded module -/

/-- Restriction of scalars along `R ⟶ O`, landing in sheaves for the chaotic topology. -/
def restrictFunctor : PresheafOfModules.{m} O ⥤ SheafOfModules.{m} R :=
  PresheafOfModules.restrictScalars (scalarHom D) ⋙
    (Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence R).inverse

/-- The functor from presheaves to sheaves of modules for the chaotic topology is additive. -/
instance chaoticInverse_additive :
    (Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence.{u, v, m, a} R).inverse.Additive
    where
  map_add := rfl

/-- Restriction of scalars along `R ⟶ O` is additive. -/
instance : (restrictFunctor.{a, m} D).Additive := by
  unfold restrictFunctor
  infer_instance

section OfComplex

variable (K : CochainComplex (PresheafOfModules.{m} O) ℤ)

/-- The sections over `U` of the degree-`n` term of a complex of presheaves of modules. -/
abbrev kpiece (U : Cᵒᵖ) (n : ℤ) : Type m := (K.X n).obj U

variable {K}

/-- The zero sections in degrees `p` and `q` are heterogeneously equal when `p = q`. -/
theorem kpiece_heq_zero {U : Cᵒᵖ} {p q : ℤ} (h : p = q) :
    (0 : kpiece K U p) ≍ (0 : kpiece K U q) := by
  subst h
  rfl

/-- The restriction maps of `K` commute with transport along `p = q`. -/
theorem kmap_gradedCast {U V : Cᵒᵖ} (f : U ⟶ V) {p q : ℤ} (h : p = q) (y : kpiece K U p) :
    (K.X q).map f (gradedCast (kpiece K U) h y) =
      gradedCast (kpiece K V) h ((K.X p).map f y) := by
  subst h
  rfl

/-- The differential of `K` commutes with transport along `p = q`. -/
theorem kd_gradedCast {U : Cᵒᵖ} {p q : ℤ} (h : p = q) (y : kpiece K U p) :
    (K.d q (q + 1)).app U (gradedCast (kpiece K U) h y) =
      gradedCast (kpiece K U) (congrArg (· + 1) h) ((K.d p (p + 1)).app U y) := by
  subst h
  rfl

/-- A morphism of complexes commutes with transport along `p = q`. -/
theorem kf_gradedCast {L : CochainComplex (PresheafOfModules.{m} O) ℤ} (g : K ⟶ L) {U : Cᵒᵖ}
    {p q : ℤ} (h : p = q) (y : kpiece K U p) :
    (g.f q).app U (gradedCast (kpiece K U) h y) =
      gradedCast (kpiece L U) h ((g.f p).app U y) := by
  subst h
  rfl

variable (K)

/-- The right action of the degree-zero sections of `A` on the degree-`n` sections of `K`:
the action of the corresponding sections of `O`, read in degree `n + 0`. -/
def kact0 (n : ℤ) (U : Cᵒᵖ) :
    kpiece K U n →+ (A.complex.X 0).val.obj U →+ kpiece K U (n + 0) :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun y => gradedCast (kpiece K U) (add_zero n).symm ((D.ψ U).symm y • x))
      (fun y y' => by rw [map_add, add_smul, gradedCast_add]))
    (fun x x' => by
      ext y
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, smul_add, gradedCast_add])

/-- A degree-zero section `y` of `A` acts on `x` as `ψ⁻¹ y • x`, read in degree `n + 0`. -/
theorem kact0_apply (n : ℤ) (U : Cᵒᵖ) (x : kpiece K U n) (y : (A.complex.X 0).val.obj U) :
    kact0 D K n U x y = gradedCast (kpiece K U) (add_zero n).symm ((D.ψ U).symm y • x) := rfl

/-- The right action of the sections of `A` on the sections of `K`; it vanishes outside degree
zero, where the pieces of `A` vanish. -/
def kact (n i : ℤ) (U : Cᵒᵖ) :
    kpiece K U n →+ (A.complex.X i).val.obj U →+ kpiece K U (n + i) :=
  if h : i = 0 then by subst h; exact kact0 D K n U else 0

/-- In degree zero, `kact` is `kact0`. -/
theorem kact_zero_deg (n : ℤ) (U : Cᵒᵖ) : kact D K n 0 U = kact0 D K n U := by
  simp [kact]

/-- In a nonzero degree `i`, `kact` vanishes. -/
theorem kact_of_ne {n i : ℤ} (h : i ≠ 0) (U : Cᵒᵖ) : kact D K n i U = 0 := by
  simp [kact, h]

end OfComplex

/-- The inverse of `ψ` carries the scalar action of `r` to multiplication by its image in `O`. -/
theorem ψ_symm_smul (U : Cᵒᵖ) (r : R.obj.obj U) (y : (A.complex.X 0).val.obj U) :
    (D.ψ U).symm (r • y) = scalarRingHom D U r * (D.ψ U).symm y := by
  apply (D.ψ U).injective
  rw [ψ_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The inverse of `ψ` commutes with the restriction maps. -/
theorem ψ_symm_map {U V : Cᵒᵖ} (f : U ⟶ V) (y : (A.complex.X 0).val.obj U) :
    (D.ψ V).symm ((A.complex.X 0).val.map f y) = O.map f ((D.ψ U).symm y) := by
  apply (D.ψ V).injective
  refine ((D.ψ V).apply_symm_apply _).trans ?_
  rw [D.ψ_map, AddEquiv.apply_symm_apply]

/-- The inverse of `ψ` carries the multiplication of `A` in degrees `0, 0` to that of `O`. -/
theorem ψ_symm_mul (U : Cᵒᵖ) (y z : (A.complex.X 0).val.obj U) :
    (D.ψ U).symm ((A.mul 0 0).app U y z) = (D.ψ U).symm y * (D.ψ U).symm z := by
  apply (D.ψ U).injective
  rw [AddEquiv.apply_symm_apply, D.ψ_mul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The inverse of `ψ` carries the unit of `A` to the unit of `O`. -/
theorem ψ_symm_one (U : Cᵒᵖ) : (D.ψ U).symm (A.one.eval U) = 1 := by
  rw [← D.ψ_one, AddEquiv.symm_apply_apply]

section OfComplexStructure

variable {K : CochainComplex (PresheafOfModules.{m} O) ℤ}

include D in
/-- The actions of two sections of `O` on a section of `K` commute. -/
theorem smul_comm' {U : Cᵒᵖ} {n : ℤ} (b c : O.obj U) (x : kpiece K U n) :
    b • c • x = c • b • x := by
  rw [smul_smul, D.comm, ← smul_smul]

/-- `kact` is linear over `R` in the section of `K`. -/
theorem kact_smul_left (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : kpiece K U n)
    (y : (A.complex.X i).val.obj U) :
    kact D K n i U (scalarRingHom D U r • x) y = scalarRingHom D U r • kact D K n i U x y := by
  by_cases hi : i = 0
  · subst hi
    rw [kact_zero_deg, kact0_apply, kact0_apply, smul_comm' D, gradedCast_smul]
  · simp [kact_of_ne D K hi]

/-- `kact` is linear over `R` in the section of `A`. -/
theorem kact_smul_right (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : kpiece K U n)
    (y : (A.complex.X i).val.obj U) :
    kact D K n i U x (r • y) = scalarRingHom D U r • kact D K n i U x y := by
  by_cases hi : i = 0
  · subst hi
    rw [kact_zero_deg, kact0_apply, kact0_apply, ψ_symm_smul, mul_smul, gradedCast_smul]
  · simp [kact_of_ne D K hi]

/-- `kact` commutes with the restriction maps. -/
theorem kact_naturality (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (x : kpiece K U n)
    (y : (A.complex.X i).val.obj U) :
    (K.X (n + i)).map f (kact D K n i U x y) =
      kact D K n i V ((K.X n).map f x) ((A.complex.X i).val.map f y) := by
  by_cases hi : i = 0
  · subst hi
    simp only [kact_zero_deg, kact0_apply, kmap_gradedCast, PresheafOfModules.map_smul]
    rw [← ψ_symm_map]
    rfl
  · rw [kact_of_ne D K hi, kact_of_ne D K hi]
    exact map_zero _

/-- `kact` is associative: `(x · y) · z ≍ x · (y z)`. -/
theorem kact_assoc (n i j : ℤ) (U : Cᵒᵖ) (x : kpiece K U n) (y : (A.complex.X i).val.obj U)
    (z : (A.complex.X j).val.obj U) :
    kact D K (n + i) j U (kact D K n i U x y) z ≍
      kact D K n (i + j) U x ((A.mul i j).app U y z) := by
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst hi hj
      have h00 : kact D K n (0 + 0) U = kact0 D K n U := kact_zero_deg D K n U
      rw [kact_zero_deg, kact_zero_deg, h00, kact0_apply, kact0_apply, kact0_apply,
        ψ_symm_mul, ← gradedCast_smul, gradedCast_trans]
      refine (gradedCast_heq _ _ _).trans (HEq.trans (heq_of_eq ?_) (gradedCast_heq _ _ _).symm)
      rw [mul_smul, smul_comm' D]
    · obtain rfl := eq_zero_of_ne_zero_deg D hj z
      simp only [map_zero]
      exact kpiece_heq_zero (add_assoc n i j)
  · obtain rfl := eq_zero_of_ne_zero_deg D hi y
    simp only [map_zero, AddMonoidHom.zero_apply]
    exact kpiece_heq_zero (add_assoc n i j)

/-- The unit of `A` acts on `K` as the identity. -/
theorem kact_one (n : ℤ) (U : Cᵒᵖ) (x : kpiece K U n) :
    kact D K n 0 U x (A.one.eval U) ≍ x := by
  rw [kact_zero_deg, kact0_apply, ψ_symm_one, one_smul]
  exact gradedCast_heq _ _ _

/-- The Leibniz rule for `kact`: `d (x · y) = d x · y + (-1)^n x · d y`, read in degree
`n + i + 1`. -/
theorem kact_leibniz (n i : ℤ) (U : Cᵒᵖ) (x : kpiece K U n) (y : (A.complex.X i).val.obj U) :
    (K.d (n + i) (n + i + 1)).app U (kact D K n i U x y) =
      gradedCast (kpiece K U) (add_right_comm n 1 i)
          (kact D K (n + 1) i U ((K.d n (n + 1)).app U x) y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (kpiece K U) (add_assoc n i 1).symm
            (kact D K n (i + 1) U x ((A.complex.d i (i + 1)).val.app U y)) := by
  by_cases hi : i = 0
  · subst hi
    have hdy : (A.complex.d 0 (0 + 1)).val.app U y = 0 :=
      eq_zero_of_ne_zero_deg D (by omega) _
    simp only [hdy, map_zero, gradedCast_zero, smul_zero, add_zero, kact_zero_deg, kact0_apply,
      kd_gradedCast, map_smul, gradedCast_trans]
  · obtain rfl := eq_zero_of_ne_zero_deg D hi y
    simp only [map_zero, gradedCast_zero, smul_zero, add_zero]

end OfComplexStructure

/-- **A cochain complex of presheaves of `O`-modules, read as a right differential graded
`A`-module**: its underlying complex of `R`-modules is obtained by restricting scalars along
`R ⟶ O`, and a degree-zero section of `A` acts through the corresponding section of `O`. -/
def ofComplex (K : CochainComplex (PresheafOfModules.{m} O) ℤ) :
    DifferentialGradedModule.{a, a, m} A where
  complex := ((restrictFunctor D).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  mul n i :=
    { app := fun U => kact D K n i U
      map_smul_left := fun U r x y => kact_smul_left D n i U r x y
      map_smul_right := fun U r x y => kact_smul_right D n i U r x y
      naturality := fun f x y => kact_naturality D n i f x y }
  mul_assoc n i j U x y z := kact_assoc D n i j U x y z
  mul_one n U x := kact_one D n U x
  leibniz n i U x y := kact_leibniz D n i U x y

/-- The right action of `A` on `ofComplex D K` is `kact`. -/
theorem ofComplex_mul_app (K : CochainComplex (PresheafOfModules.{m} O) ℤ) (n i : ℤ)
    (U : Cᵒᵖ) : ((ofComplex D K).mul n i).app U = kact D K n i U := rfl

/-- A morphism of complexes commutes with `kact`. -/
theorem kact_map {K L : CochainComplex (PresheafOfModules.{m} O) ℤ} (g : K ⟶ L) (n i : ℤ)
    (U : Cᵒᵖ) (x : kpiece K U n) (y : (A.complex.X i).val.obj U) :
    (g.f (n + i)).app U (kact D K n i U x y) = kact D L n i U ((g.f n).app U x) y := by
  by_cases hi : i = 0
  · subst hi
    simp only [kact_zero_deg, kact0_apply, kf_gradedCast, map_smul]
  · simp [kact_of_ne D K hi, kact_of_ne D L hi]

/-- A morphism of complexes of presheaves of `O`-modules, as a homomorphism of right
differential graded `A`-modules. -/
def ofComplexMap {K L : CochainComplex (PresheafOfModules.{m} O) ℤ} (g : K ⟶ L) :
    ofComplex D K ⟶ ofComplex D L where
  toHomologicalComplex := ((restrictFunctor D).mapHomologicalComplex (ComplexShape.up ℤ)).map g
  map_mul n i U x y := kact_map D g n i U x y

/-- **Cochain complexes of presheaves of `O`-modules as right differential graded
`A`-modules**, as a functor. -/
def ofComplexFunctor :
    CochainComplex (PresheafOfModules.{m} O) ℤ ⥤ DifferentialGradedModule.{a, a, m} A where
  obj K := ofComplex D K
  map g := ofComplexMap D g
  map_id _ := DifferentialGradedModule.Hom.ext fun _ => (restrictFunctor D).map_id _
  map_comp _ _ := DifferentialGradedModule.Hom.ext fun _ => (restrictFunctor D).map_comp _ _

/-! ### The two constructions are mutually inverse -/

/-- The action of `O` on `ofComplex D K` recovers the module structure of `K`. -/
theorem act_ofComplex (K : CochainComplex (PresheafOfModules.{m} O) ℤ) (U : Cᵒᵖ) (n : ℤ)
    (b : O.obj U) (x : kpiece K U n) :
    act D (ofComplex D K) U n b x = b • x := by
  unfold act
  rw [ofComplex_mul_app, kact_zero_deg]
  exact eq_of_heq ((gradedCast_heq _ _ _).trans ((gradedCast_heq _ _ _).trans
    (heq_of_eq (by rw [AddEquiv.symm_apply_apply]))))

/-- The identity of underlying sections, as an isomorphism of presheaves of modules, when the two
module structures agree. -/
def isoOfSmulEq {P Q : PresheafOfModules.{m} O} (e : ∀ U, P.obj U ≃+ Q.obj U)
    (he : ∀ U (b : O.obj U) (x : P.obj U), e U (b • x) = b • e U x)
    (hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : P.obj U), e V (P.map f x) = Q.map f (e U x)) :
    P ≅ Q :=
  PresheafOfModules.isoMk (fun U => LinearEquiv.toModuleIso
    { e U with map_smul' := he U })
    (fun U V f => by
      ext x
      exact hnat f x)

/-- The counit: reading a complex of presheaves of `O`-modules as a differential graded module and
back gives the complex itself. -/
def toComplexOfComplexIso (K : CochainComplex (PresheafOfModules.{m} O) ℤ) :
    toComplex D (ofComplex D K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => isoOfSmulEq (fun U => AddEquiv.refl _)
      (fun U b x => act_ofComplex D K U n b x) (fun f x => rfl))
    (fun i j _ => by
      ext U x
      rfl)

/-- The image of `r` in `O` acts on `M` as the scalar action of `r`. -/
theorem act_scalar (M : DifferentialGradedModule.{a, a, m} A) (U : Cᵒᵖ) (n : ℤ)
    (r : R.obj.obj U) (x : piece M U n) :
    act D M U n (scalarRingHom D U r) x = r • x := by
  unfold act
  rw [ψ_scalarRingHom, (M.mul n 0).map_smul_right, gradedCast_smul]
  congr 1
  exact (gradedCast_eq_iff_heq _ _ _).2 (M.mul_one n U x)

/-- The action `kact` on `toComplex D M` is the right action of `A` on `M`. -/
theorem kact_toComplex (M : DifferentialGradedModule.{a, a, m} A) (n i : ℤ) (U : Cᵒᵖ)
    (x : piece M U n) (y : (A.complex.X i).val.obj U) :
    kact D (toComplex D M) n i U x y = (M.mul n i).app U x y := by
  by_cases hi : i = 0
  · subst hi
    rw [kact_zero_deg]
    refine eq_of_heq ((gradedCast_heq _ _ _).trans ((act_heq D _ x).trans (heq_of_eq ?_)))
    rw [AddEquiv.apply_symm_apply]
  · obtain rfl := eq_zero_of_ne_zero_deg D hi y
    rw [kact_of_ne D _ hi]
    exact (map_zero ((M.mul n i).app U x)).symm

/-- The identity of the underlying complex, as an isomorphism of the complexes of sheaves of
`R`-modules underlying `M` and the module attached to the complex of `M`. -/
def ofComplexToComplexComplexIso (M : DifferentialGradedModule.{a, a, m} A) :
    (ofComplex D (toComplex D M)).complex ≅ M.complex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := ⟨PresheafOfModules.homMk (𝟙 _) (fun U r x => act_scalar D M U n r x)⟩
        inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun U r x => (act_scalar D M U n r x).symm)⟩
        hom_inv_id := by
          ext U x
          rfl
        inv_hom_id := by
          ext U x
          rfl })
    (fun i j _ => by
      ext U x
      rfl)

/-- The unit: reading a differential graded module as a complex and back gives the module. -/
def ofComplexToComplexIso (M : DifferentialGradedModule.{a, a, m} A) :
    ofComplex D (toComplex D M) ≅ M where
  hom :=
    { toHomologicalComplex := (ofComplexToComplexComplexIso D M).hom
      map_mul := fun n i U x y => kact_toComplex D M n i U x y }
  inv :=
    { toHomologicalComplex := (ofComplexToComplexComplexIso D M).inv
      map_mul := fun n i U x y => (kact_toComplex D M n i U x y).symm }
  hom_inv_id := DifferentialGradedModule.Hom.ext fun n =>
    congrArg (fun φ => φ.f n) (ofComplexToComplexComplexIso D M).hom_inv_id
  inv_hom_id := DifferentialGradedModule.Hom.ext fun n =>
    congrArg (fun φ => φ.f n) (ofComplexToComplexComplexIso D M).inv_hom_id

/-- **Right differential graded modules over an algebra concentrated in degree zero are cochain
complexes of modules** over the corresponding presheaf of commutative rings: the identification
`Mod(O, 0) = Comp(O)` of Section 24.33 of the Stacks project. -/
def equivalence :
    DifferentialGradedModule.{a, a, m} A ≌ CochainComplex (PresheafOfModules.{m} O) ℤ :=
  CategoryTheory.Equivalence.mk (toComplexFunctor D) (ofComplexFunctor D)
    (NatIso.ofComponents (fun M => (ofComplexToComplexIso D M).symm)
      (fun f => DifferentialGradedModule.Hom.ext fun n => by
        ext U x
        rfl))
    (NatIso.ofComponents (fun K => toComplexOfComplexIso D K)
      (fun g => by
        ext n U x
        rfl))

/-- The functor of `equivalence D` is `toComplexFunctor D`. -/
@[simp]
theorem equivalence_functor : (equivalence D).functor = toComplexFunctor D := rfl

/-- The inverse of `equivalence D` is `ofComplexFunctor D`. -/
@[simp]
theorem equivalence_inverse : (equivalence D).inverse = ofComplexFunctor D := rfl

/-! ### Quasi-isomorphisms and homotopies -/

/-- Restriction of scalars along `R ⟶ O` reflects isomorphisms. -/
instance restrictFunctor_reflectsIsomorphisms :
    (restrictFunctor.{a, m} D).ReflectsIsomorphisms := by
  unfold restrictFunctor
  infer_instance

section QuasiIso

variable [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Restriction of scalars along `R ⟶ O` preserves homology. -/
instance restrictFunctor_preservesHomology : (restrictFunctor.{a, m} D).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  exact fun S hS => (hS.map (PresheafOfModules.restrictScalars (scalarHom D))).map
    (Stacks.ModulesOnACategory.chaoticSheafPresheafEquivalence.{u, v, m, a} R).inverse

omit [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m}]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The underlying complex of `M` is the restriction of scalars of the complex of `M`, naturally
in `M`. -/
theorem toHomologicalComplex_arrow_iso {M N : DifferentialGradedModule.{a, a, m} A} (f : M ⟶ N) :
    (ofComplexToComplexComplexIso D M).inv ≫
        ((restrictFunctor D).mapHomologicalComplex (ComplexShape.up ℤ)).map (toComplexMap D f) =
      f.toHomologicalComplex ≫ (ofComplexToComplexComplexIso D N).inv := by
  ext n U x
  rfl

/-- **A homomorphism of right differential graded modules is a quasi-isomorphism of the underlying
complexes of `R`-modules exactly when it is one of the complexes of `O`-modules.** -/
theorem quasiIso_toComplexMap_iff {M N : DifferentialGradedModule.{a, a, m} A} (f : M ⟶ N) :
    QuasiIso (toComplexMap D f) ↔ QuasiIso f.toHomologicalComplex := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology (toComplexMap D f)
    (restrictFunctor D)]
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (ofComplexToComplexComplexIso D M) (ofComplexToComplexComplexIso D N)
      (by ext n U x; rfl))

end QuasiIso

/-- The components of a difference of morphisms of sheaves of modules are the differences of
their components. -/
theorem val_sub_app {P Q : SheafOfModules.{m} R} (φ ψ : P ⟶ Q) (U : Cᵒᵖ) (x : P.val.obj U) :
    (φ - ψ).val.app U x = φ.val.app U x - ψ.val.app U x := by
  rw [show (φ - ψ).val = φ.val - ψ.val from (SheafOfModules.forget R).map_sub]
  rfl

/-- The components of a sum of morphisms of sheaves of modules are the sums of their
components. -/
theorem val_add_app {P Q : SheafOfModules.{m} R} (φ ψ : P ⟶ Q) (U : Cᵒᵖ) (x : P.val.obj U) :
    (φ + ψ).val.app U x = φ.val.app U x + ψ.val.app U x := by
  rw [show (φ + ψ).val = φ.val + ψ.val from (SheafOfModules.forget R).map_add]
  rfl

section Homotopy

variable {M N : DifferentialGradedModule.{a, a, m} A} {f g : M ⟶ N}

/-- A homotopy applied to a section transported along `p = q` agrees, up to heterogeneous
equality, with its value on the original section. -/
theorem happ_gradedCast (h : DifferentialGradedModule.Homotopy f g) (U : Cᵒᵖ) {p q : ℤ}
    (e : p = q) (y : piece M U p) :
    (h.app q).val.app U (gradedCast (piece M U) e y) ≍ (h.app p).val.app U y := by
  subst e
  rfl

/-- The components of a homotopy are linear for the action of `O`. -/
theorem happ_act (h : DifferentialGradedModule.Homotopy f g) (U : Cᵒᵖ) (n : ℤ) (b : O.obj U)
    (x : piece M U n) :
    (h.app n).val.app U (act D M U n b x) = act D N U (n - 1) b ((h.app n).val.app U x) :=
  eq_of_heq <| (happ_gradedCast h U (add_zero n) _).trans
    ((h.map_mul n 0 U x (D.ψ U b)).trans (act_heq D b _).symm)

/-- The component of a homotopy, as a morphism of presheaves of `O`-modules. -/
def homotopyPiece (h : DifferentialGradedModule.Homotopy f g) (n : ℤ) :
    toPiece D M n ⟶ toPiece D N (n - 1) :=
  PresheafOfModules.homMk (addPresheafMap (h.app n)) (fun U b x => happ_act D h U n b x)

/-- The morphism `eqToHom` between the pieces `toPiece D N p` and `toPiece D N q` is transport
along `p = q`. -/
theorem eqToHom_toPiece_app {p q : ℤ} (e : p = q) (U : Cᵒᵖ) (y : (toPiece D N p).obj U) :
    (eqToHom (congrArg (toPiece D N) e)).app U y = gradedCast (piece N U) e y := by
  subst e
  rfl

/-- The morphism `eqToHom` between the pieces of `N` in degrees `p` and `q` is transport along
`p = q`. -/
theorem eqToHom_X_app {p q : ℤ} (e : p = q) (U : Cᵒᵖ) (y : piece N U p) :
    (eqToHom (congrArg N.complex.X e)).val.app U y = gradedCast (piece N U) e y := by
  subst e
  rfl

/-- The components of the homotopy of complexes of `O`-modules attached to a homotopy. -/
def homotopyHom (h : DifferentialGradedModule.Homotopy f g) (i j : ℤ) :
    (toComplex D M).X i ⟶ (toComplex D N).X j :=
  if hij : j + 1 = i then
    homotopyPiece D h i ≫ eqToHom (congrArg (toPiece D N) (by omega : i - 1 = j)) else 0

/-- For `j + 1 = i`, the component `homotopyHom D h i j` is the component of `h` in degree `i`,
transported to degree `j`. -/
theorem homotopyHom_app (h : DifferentialGradedModule.Homotopy f g) {i j : ℤ} (hij : j + 1 = i)
    (U : Cᵒᵖ) (x : (toPiece D M i).obj U) :
    (homotopyHom D h i j).app U x =
      gradedCast (piece N U) (by omega : i - 1 = j) ((h.app i).val.app U x) := by
  unfold homotopyHom
  rw [dite_eq_left hij]
  exact eqToHom_toPiece_app D _ U _

/-- The components of a composite of morphisms of sheaves of modules are the composites of their
components. -/
theorem val_comp_app {P Q T : SheafOfModules.{m} R} (φ : P ⟶ Q) (ψ : Q ⟶ T) (U : Cᵒᵖ)
    (x : P.val.obj U) : (φ ≫ ψ).val.app U x = ψ.val.app U (φ.val.app U x) := rfl

/-- **A homotopy of homomorphisms of right differential graded modules is a homotopy of the
complexes of `O`-modules.** -/
def homotopyToComplex (h : DifferentialGradedModule.Homotopy f g) :
    _root_.Homotopy (toComplexMap D f) (toComplexMap D g) where
  hom := homotopyHom D h
  zero i j hij := by
    change ¬ (j + 1 = i) at hij
    unfold homotopyHom
    rw [dite_eq_right hij]
  comm i := by
    rw [dNext_eq _ (ComplexShape.up_mk i (i + 1) (by omega)),
      prevD_eq _ (ComplexShape.up_mk (i - 1) i (by omega))]
    have hc := h.comm i
    have key : ∀ (U : Cᵒᵖ) (x : piece M U i), (f.toHomologicalComplex.f i).val.app U x =
        gradedCast (piece N U) (by omega : i + 1 - 1 = i)
            ((h.app (i + 1)).val.app U ((M.complex.d i (i + 1)).val.app U x)) +
          (N.complex.d (i - 1) i).val.app U ((h.app i).val.app U x) +
          (g.toHomologicalComplex.f i).val.app U x := by
      intro U x
      have hx := congrArg (fun φ => φ.val.app U x) hc
      rw [val_sub_app, val_add_app, val_comp_app, val_comp_app, val_comp_app] at hx
      rw [eq_add_of_sub_eq hx, add_comm ((N.complex.d (i - 1) i).val.app U _)]
      congr 2
      exact eqToHom_X_app _ U _
    ext U x
    simp only [PresheafOfModules.add_app, PresheafOfModules.comp_app, ModuleCat.hom_add,
      ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply]
    refine (key U x).trans ?_
    congr 2
    · exact (homotopyHom_app D h (by omega : i + 1 = i + 1) U _).symm
    · exact congrArg _ (homotopyHom_app D h (by omega : i - 1 + 1 = i) U x).symm

end Homotopy

end DegreeZero

end DifferentialGradedModule

end SheafOfModules

end
