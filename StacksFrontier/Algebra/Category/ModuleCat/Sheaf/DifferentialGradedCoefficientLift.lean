module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleStructures
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedOppositeAlgebra
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedOppositeModule

/-!
# Differential graded modules do not depend on the base ring

Let `α : R ⟶ R'` be a morphism between the sheaves of rings underlying two sheaves of commutative
rings on a site and let `B` be a sheaf of differential graded `R'`-algebras. Restricting scalars
along `α` makes `B` a sheaf of differential graded `R`-algebras `B♭` with the same cochain complex
and the same multiplication, and makes every right differential graded `B`-module a right
differential graded `B♭`-module. This file proves that the second construction is an equivalence
onto all right differential graded `B♭`-modules: a section `r` of `R'` acts on a right
differential graded `B♭`-module `E` as right multiplication by `r · 1`, which makes `E` a right
differential graded `B`-module `E♯` restricting back to `E`, and a homomorphism of right
differential graded `B♭`-modules between restrictions is automatically `R'`-linear.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.restrictCoeff`: `B♭`, the restriction of scalars of a
  sheaf of differential graded algebras along a morphism of sheaves of rings.
* `SheafOfModules.DifferentialGradedModule.restrictCoeff`: the restriction of scalars of a right
  differential graded module, and `restrictCoeffFunctor` the functor.
* `SheafOfModules.DifferentialGradedModule.liftCoeff`: `E♯`, the lift of a right differential
  graded `B♭`-module to a right differential graded `B`-module.

## Main results

* `SheafOfModules.DifferentialGradedModule.restrictLiftComplexIso`: the complex of `E♯` restricts
  back to the complex of `E`.
* `SheafOfModules.DifferentialGradedModule.liftCoeffHomEquiv`: homomorphisms `E♯ ⟶ Q` of right
  differential graded `B`-modules are the homomorphisms `E ⟶ Q♭` of right differential graded
  `B♭`-modules.
* `SheafOfModules.acyclic_of_acyclic_coeffRestrict`: a complex of sheaves of `R'`-modules is
  acyclic as soon as its restriction of scalars is.
* `SheafOfModules.DifferentialGradedModule.acyclic_of_corepresentableBy_restrictCoeff`: a right
  differential graded `B`-module corepresenting `F` precomposed with restriction of scalars is
  acyclic as soon as a corepresenting object of `F` is.

## Implementation notes

This is the step of the source's proof of Tag 0FSI (2) that reads `f⁻¹P ⊗_{f⁻¹A} A'` as a
differential graded `A'`-module although the tensor product is formed over `f⁻¹O`: the right
action of `A'` determines the action of `O'`.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

universe t a m a₁ a₂ a₃ v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {R R' : Sheaf J CommRingCat.{t}} (α : toRingCat J R ⟶ toRingCat J R')

/-- The morphism of sheaves of rings `α`, under the name the restriction of scalars along it is
written with. -/
abbrev toRingCatHom : toRingCat J R ⟶ toRingCat J R' := α

/-- Restriction of scalars of sheaves of modules along a morphism of sheaves of commutative
rings. -/
noncomputable abbrev restrictCoeffSheaf :
    SheafOfModules.{a} (toRingCat J R') ⥤ SheafOfModules.{a} (toRingCat J R) :=
  restrictScalars (toRingCatHom α)

/-- A bilinear map of sheaves of `R'`-modules is bilinear over `R` for the restricted
structures. -/
def restrictBilinear {M : SheafOfModules.{a₁} (toRingCat J R')}
    {N : SheafOfModules.{a₂} (toRingCat J R')} {P : SheafOfModules.{a₃} (toRingCat J R')}
    (β : BilinearMap M N P) :
    BilinearMap ((restrictCoeffSheaf α).obj M)
      ((restrictCoeffSheaf α).obj N) ((restrictCoeffSheaf α).obj P) where
  app U := β.app U
  map_smul_left U r x y := β.map_smul_left U ((α.hom.app U).hom r) x y
  map_smul_right U r x y := β.map_smul_right U ((α.hom.app U).hom r) x y
  naturality f x y := β.naturality f x y

/-- The restricted bilinear map has the same components as `β`. -/
@[simp]
theorem restrictBilinear_app {M : SheafOfModules.{a₁} (toRingCat J R')}
    {N : SheafOfModules.{a₂} (toRingCat J R')} {P : SheafOfModules.{a₃} (toRingCat J R')}
    (β : BilinearMap M N P) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (restrictBilinear α β).app U x y = β.app U x y :=
  rfl

namespace DifferentialGradedAlgebra

/-- **The restriction of scalars `B♭` of a sheaf of differential graded `R'`-algebras along
`α : R ⟶ R'`**: the same cochain complex with scalars restricted, and the same multiplication. -/
noncomputable def restrictCoeff (B : DifferentialGradedAlgebra.{t, a} (toRingCat J R')) :
    DifferentialGradedAlgebra.{t, a} (toRingCat J R) where
  complex := ((restrictCoeffSheaf α).mapHomologicalComplex _).obj B.complex
  mul n i := restrictBilinear α (B.mul n i)
  one := B.one
  mul_assoc := B.mul_assoc
  one_mul := B.one_mul
  mul_one := B.mul_one
  leibniz := B.leibniz

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {α} {B : DifferentialGradedAlgebra.{t, a} (toRingCat J R')}

/-- **The restriction of scalars of a right differential graded `B`-module**, a right
differential graded `B♭`-module with the same complex and the same action. -/
noncomputable def restrictCoeff (Q : DifferentialGradedModule.{t, a, m} B) :
    DifferentialGradedModule.{t, a, m} (B.restrictCoeff α) where
  complex := ((restrictCoeffSheaf α).mapHomologicalComplex _).obj Q.complex
  mul n i := restrictBilinear α (Q.mul n i)
  mul_assoc := Q.mul_assoc
  mul_one := Q.mul_one
  leibniz := Q.leibniz

variable (α) in
/-- Restriction of scalars as a functor. -/
noncomputable def restrictCoeffFunctor :
    DifferentialGradedModule.{t, a, m} B ⥤
      DifferentialGradedModule.{t, a, m} (B.restrictCoeff α) where
  obj Q := Q.restrictCoeff
  map g :=
    { toHomologicalComplex :=
        ((restrictCoeffSheaf α).mapHomologicalComplex _).map g.toHomologicalComplex
      map_mul := g.map_mul }

/-! ### Lifting a module over the restricted algebra -/

section Lift

variable (L : DifferentialGradedModule.{t, a, m} (B.restrictCoeff α))

/-- Two values of the action of `L` at heterogeneously equal arguments of equal degrees are
heterogeneously equal. -/
theorem mul_heq_of_heq {n n' i i' : ℤ} (hn : n = n') (hi : i = i') (U : Cᵒᵖ)
    {x : (L.complex.X n).val.obj U} {x' : (L.complex.X n').val.obj U} (hx : x ≍ x')
    {y : (B.complex.X i).val.obj U} {y' : (B.complex.X i').val.obj U} (hy : y ≍ y') :
    (L.mul n i).app U x y ≍ (L.mul n' i').app U x' y' := by
  subst hn hi
  cases hx
  cases hy
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Two products in `B` at heterogeneously equal arguments of equal degrees are heterogeneously
equal. -/
theorem _root_.SheafOfModules.DifferentialGradedAlgebra.mul_heq_of_heq
    {R₀ : Sheaf J RingCat.{t}} (B₀ : DifferentialGradedAlgebra.{t, a} R₀) {n n' i i' : ℤ}
    (hn : n = n') (hi : i = i') (U : Cᵒᵖ)
    {x : (B₀.complex.X n).val.obj U} {x' : (B₀.complex.X n').val.obj U} (hx : x ≍ x')
    {y : (B₀.complex.X i).val.obj U} {y' : (B₀.complex.X i').val.obj U} (hy : y ≍ y') :
    (B₀.mul n i).app U x y ≍ (B₀.mul n' i').app U x' y' := by
  subst hn hi
  cases hx
  cases hy
  rfl

/-- A scalar multiple commutes with a heterogeneous equality of sections of two equal degrees of
a graded family of modules. -/
theorem heq_smul_of_heq {ι : Type*} (T : ι → Type*) {S : Type*} [∀ k, SMul S (T k)] {k k' : ι}
    (hk : k = k') (s : S) {x : T k} {y : T k'} (hxy : x ≍ y) : s • x ≍ s • y :=
  _root_.SheafOfModules.heq_dependent_apply (fun k (z : T k) ↦ s • z) hk hxy

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- In a sheaf of differential graded algebras, `(s · 1) · y = s • y`. -/
theorem _root_.SheafOfModules.DifferentialGradedAlgebra.smul_one_mul_heq
    {R₀ : Sheaf J RingCat.{t}} (B₀ : DifferentialGradedAlgebra.{t, a} R₀) (i : ℤ) (U : Cᵒᵖ)
    (s : R₀.obj.obj U) (y : (B₀.complex.X i).val.obj U) :
    (B₀.mul 0 i).app U (s • B₀.one.eval U) y ≍ s • y := by
  rw [(B₀.mul 0 i).map_smul_left]
  exact heq_smul_of_heq (fun q ↦ (B₀.complex.X q).val.obj U) (zero_add i) s (B₀.one_mul i U y)

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- In a sheaf of differential graded algebras, `y · (s · 1) = s • y`. -/
theorem _root_.SheafOfModules.DifferentialGradedAlgebra.mul_smul_one_heq
    {R₀ : Sheaf J RingCat.{t}} (B₀ : DifferentialGradedAlgebra.{t, a} R₀) (i : ℤ) (U : Cᵒᵖ)
    (s : R₀.obj.obj U) (y : (B₀.complex.X i).val.obj U) :
    (B₀.mul i 0).app U y (s • B₀.one.eval U) ≍ s • y := by
  rw [(B₀.mul i 0).map_smul_right]
  exact heq_smul_of_heq (fun q ↦ (B₀.complex.X q).val.obj U) (add_zero i) s (B₀.mul_one i U y)

/-- If `a = b + c` in one degree and all three are heterogeneously equal to `e` in an equal
degree, then `e = e + e`. -/
theorem eq_add_of_heq {ι : Type*} (T : ι → Type*) [∀ k, Add (T k)] {k k' : ι} (hk : k = k')
    {a b c : T k} {e : T k'} (ha : a ≍ e) (hb : b ≍ e) (hc : c ≍ e) (habc : a = b + c) :
    e = e + e := by
  subst hk
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  obtain rfl := eq_of_heq hc
  exact habc

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- The differential of a sheaf of differential graded algebras kills the unit. -/
theorem _root_.SheafOfModules.DifferentialGradedAlgebra.d_one_eval
    {R₀ : Sheaf J RingCat.{t}} (B₀ : DifferentialGradedAlgebra.{t, a} R₀) (U : Cᵒᵖ) :
    (B₀.complex.d 0 (0 + 1)).val.app U (B₀.one.eval U) = 0 := by
  set e := (B₀.complex.d 0 (0 + 1)).val.app U (B₀.one.eval U) with he
  have h := B₀.leibniz 0 0 U (B₀.one.eval U) (B₀.one.eval U)
  have hl : (B₀.complex.d (0 + 0) (0 + 0 + 1)).val.app U
      ((B₀.mul 0 0).app U (B₀.one.eval U) (B₀.one.eval U)) ≍ e :=
    _root_.SheafOfModules.heq_dependent_apply
      (fun k (z : (B₀.complex.X k).val.obj U) ↦ (B₀.complex.d k (k + 1)).val.app U z)
      (add_zero 0) (B₀.one_mul 0 U (B₀.one.eval U))
  have h1 : gradedCast (fun q ↦ (B₀.complex.X q).val.obj U) (add_right_comm (0 : ℤ) 1 0)
      ((B₀.mul (0 + 1) 0).app U e (B₀.one.eval U)) ≍ e :=
    (gradedCast_heq _ _ _).trans (B₀.mul_one (0 + 1) U e)
  have h2 : gradedCast (fun q ↦ (B₀.complex.X q).val.obj U) (add_assoc (0 : ℤ) 0 1).symm
      ((B₀.mul 0 (0 + 1)).app U (B₀.one.eval U) e) ≍ e :=
    (gradedCast_heq _ _ _).trans (B₀.one_mul (0 + 1) U e)
  have key : e = e + e := by
    rw [Int.negOnePow_zero, Units.val_one, one_smul] at h
    exact eq_add_of_heq (fun q ↦ (B₀.complex.X q).val.obj U) (by norm_num) hl h1 h2 h
  exact (add_eq_left.mp key.symm)

variable (B) in
/-- The section `s · 1` of `B♭` in degree zero, for a section `s` of `R'`. -/
noncomputable def coeffOne (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U) :
    ((B.restrictCoeff α).complex.X 0).val.obj U :=
  (show (B.complex.X 0).val.obj U from s • B.one.eval U)

variable (B) in
/-- `(s + s') · 1 = s · 1 + s' · 1`. -/
theorem coeffOne_add (U : Cᵒᵖ) (s s' : (toRingCat J R').obj.obj U) :
    coeffOne (α := α) B U (s + s') = coeffOne (α := α) B U s + coeffOne (α := α) B U s' :=
  add_smul s s' (B.one.eval U)

variable (B) in
/-- `0 · 1 = 0`. -/
theorem coeffOne_zero (U : Cᵒᵖ) : coeffOne (α := α) B U 0 = 0 :=
  zero_smul _ (B.one.eval U)

variable (B) in
/-- `1 · 1` is the unit of `B♭`. -/
theorem coeffOne_one (U : Cᵒᵖ) : coeffOne (α := α) B U 1 = (B.restrictCoeff α).one.eval U :=
  one_smul _ (B.one.eval U)

/-- **The action of a section `s` of `R'` on `L`**: right multiplication by `s · 1`. -/
noncomputable def liftSMul (n : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U)
    (x : (L.complex.X n).val.obj U) : (L.complex.X n).val.obj U :=
  gradedCast (fun q ↦ (L.complex.X q).val.obj U) (add_zero n)
    ((L.mul n 0).app U x (coeffOne B U s))

/-- The action of `s` on `x` is heterogeneously equal to the product `x · (s · 1)`. -/
theorem liftSMul_heq (n : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U)
    (x : (L.complex.X n).val.obj U) :
    L.liftSMul n U s x ≍ (L.mul n 0).app U x (coeffOne B U s) := by
  unfold liftSMul
  exact gradedCast_heq _ _ _

variable {L}

/-- The action of `s` on `x` equals `y` if and only if `x · (s · 1)` is heterogeneously equal
to `y`. -/
theorem liftSMul_eq_iff (n : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U)
    (x y : (L.complex.X n).val.obj U) :
    L.liftSMul n U s x = y ↔ (L.mul n 0).app U x (coeffOne B U s) ≍ y :=
  ⟨fun h => h ▸ (L.liftSMul_heq n U s x).symm,
    fun h => eq_of_heq ((L.liftSMul_heq n U s x).trans h)⟩

/-- The section `1` of `R'` acts on `L` as the identity. -/
theorem one_liftSMul (n : ℤ) (U : Cᵒᵖ) (x : (L.complex.X n).val.obj U) :
    L.liftSMul n U 1 x = x := by
  rw [liftSMul_eq_iff, coeffOne_one]
  exact L.mul_one n U x

/-- A section of `R'` sends `0` to `0`. -/
theorem liftSMul_zero (n : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U) :
    L.liftSMul n U s 0 = 0 := by
  unfold liftSMul
  rw [map_zero, AddMonoidHom.zero_apply, gradedCast_zero]

/-- The section `0` of `R'` acts on `L` as zero. -/
theorem zero_liftSMul (n : ℤ) (U : Cᵒᵖ) (x : (L.complex.X n).val.obj U) :
    L.liftSMul n U 0 x = 0 := by
  unfold liftSMul
  rw [coeffOne_zero, map_zero, gradedCast_zero]

/-- The action of a section of `R'` on `L` is additive. -/
theorem liftSMul_add (n : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U)
    (x y : (L.complex.X n).val.obj U) :
    L.liftSMul n U s (x + y) = L.liftSMul n U s x + L.liftSMul n U s y := by
  unfold liftSMul
  rw [map_add, AddMonoidHom.add_apply, gradedCast_add]

/-- The action of `s + s'` on `L` is the sum of the actions of `s` and `s'`. -/
theorem add_liftSMul (n : ℤ) (U : Cᵒᵖ) (s s' : (toRingCat J R').obj.obj U)
    (x : (L.complex.X n).val.obj U) :
    L.liftSMul n U (s + s') x = L.liftSMul n U s x + L.liftSMul n U s' x := by
  unfold liftSMul
  rw [coeffOne_add, map_add, gradedCast_add]

/-- Right multiplication by `s · 1` on `L` is the scalar action of `s` on `B`, moved across. -/
theorem mul_liftSMul_heq (n i : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U)
    (x : (L.complex.X n).val.obj U) (y : (B.complex.X i).val.obj U) :
    (L.mul n i).app U (L.liftSMul n U s x) y ≍ (L.mul n i).app U x (s • y) := by
  refine (mul_heq_of_heq L (add_zero n).symm rfl U (L.liftSMul_heq n U s x) HEq.rfl).trans ?_
  refine (L.mul_assoc n 0 i U x (coeffOne B U s) y).trans ?_
  exact mul_heq_of_heq L rfl (zero_add i) U HEq.rfl (B.smul_one_mul_heq i U s y)

/-- The scalar action of `s` on a product is right multiplication by `s · 1`. -/
theorem liftSMul_mul_heq (n i : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U)
    (x : (L.complex.X n).val.obj U) (y : (B.complex.X i).val.obj U) :
    L.liftSMul (n + i) U s ((L.mul n i).app U x y) ≍ (L.mul n i).app U x (s • y) := by
  refine (L.liftSMul_heq (n + i) U s _).trans ?_
  refine (L.mul_assoc n i 0 U x y (coeffOne B U s)).trans ?_
  exact mul_heq_of_heq L rfl (add_zero i) U HEq.rfl (B.mul_smul_one_heq i U s y)

/-- The action of `s * s'` on `L` is the action of `s'` followed by that of `s`. -/
theorem mul_liftSMul (n : ℤ) (U : Cᵒᵖ) (s s' : (toRingCat J R').obj.obj U)
    (x : (L.complex.X n).val.obj U) :
    L.liftSMul n U (s * s') x = L.liftSMul n U s (L.liftSMul n U s' x) := by
  have hc : s' * s = s * s' := @mul_comm (R'.obj.obj U) _ s' s
  have h := (L.liftSMul_heq n U s (L.liftSMul n U s' x)).trans
    (mul_liftSMul_heq (L := L) n 0 U s' x
      (show (B.complex.X 0).val.obj U from coeffOne (α := α) B U s))
  refine eq_of_heq ((L.liftSMul_heq n U (s * s') x).trans (h.trans ?_).symm)
  refine heq_of_eq (congrArg ((L.mul n 0).app U x) ?_)
  change s' • (s • B.one.eval U) = (s * s') • B.one.eval U
  rw [smul_smul, hc]

variable (L)

variable (B) in
/-- The section `s · 1` is natural in the object of the site. -/
theorem coeffOne_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : (toRingCat J R').obj.obj X) :
    ((B.restrictCoeff α).complex.X 0).val.map f (coeffOne (α := α) B X s) =
      coeffOne (α := α) B Y ((toRingCat J R').obj.map f s) := by
  change (B.complex.X 0).val.map f (s • B.one.eval X) =
    ((toRingCat J R').obj.map f s) • B.one.eval Y
  rw [PresheafOfModules.map_smul]
  congr 1
  exact PresheafOfModules.sections_property B.one f

/-- The action of `R'` on `L` commutes with the restriction maps. -/
theorem liftSMul_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : (toRingCat J R').obj.obj X)
    (x : (L.complex.X n).val.obj X) :
    (L.complex.X n).val.map f (L.liftSMul n X s x) =
      L.liftSMul n Y ((toRingCat J R').obj.map f s) ((L.complex.X n).val.map f x) := by
  unfold liftSMul
  rw [← castHom_apply, ← castHom_apply, castHom_naturality, (L.mul n 0).naturality,
    coeffOne_naturality]

/-- The differential of `B♭` kills `s · 1`. -/
theorem d_coeffOne (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U) :
    ((B.restrictCoeff α).complex.d 0 (0 + 1)).val.app U (coeffOne (α := α) B U s) = 0 := by
  change (B.complex.d 0 (0 + 1)).val.app U (s • B.one.eval U) = 0
  rw [map_smul, B.d_one_eval, smul_zero]

/-- The differentials of `L` commute with the action of `R'`. -/
theorem d_liftSMul (i j : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U)
    (x : (L.complex.X i).val.obj U) :
    (L.complex.d i j).val.app U (L.liftSMul i U s x) =
      L.liftSMul j U s ((L.complex.d i j).val.app U x) := by
  by_cases hij : i + 1 = j
  · subst hij
    unfold liftSMul
    rw [gradedCast_d_app, L.leibniz i 0 U x (coeffOne B U s), d_coeffOne, map_zero,
      gradedCast_zero, smul_zero]
    simp only [add_zero, gradedCast_trans]
  · rw [L.complex.shape i j hij]
    change (0 : (L.complex.X i).val.obj U →+ (L.complex.X j).val.obj U)
      (L.liftSMul i U s x) = L.liftSMul j U s 0
    rw [liftSMul_zero]
    rfl

/-- The sections of `L` in degree `n` as a module over `R'`, the section `s` acting as right
multiplication by `s · 1`. -/
@[instance_reducible]
noncomputable def liftModule (n : ℤ) (U : Cᵒᵖ) :
    Module ((toRingCat J R').obj.obj U) ((L.complex.X n).val.presheaf.obj U) where
  smul s x := L.liftSMul n U s x
  one_smul := L.one_liftSMul n U
  mul_smul s s' x := L.mul_liftSMul n U s s' x
  smul_zero s := L.liftSMul_zero n U s
  smul_add s x y := L.liftSMul_add n U s x y
  add_smul s s' x := L.add_liftSMul n U s s' x
  zero_smul := L.zero_liftSMul n U

/-- **The degree-`n` piece of the lift `L♯`**: the sheaf of abelian groups of `L` in degree `n`
with the action of `R'`. -/
noncomputable def liftPiece (n : ℤ) : SheafOfModules.{m} (toRingCat J R') where
  val := @PresheafOfModules.ofPresheaf C _ (toRingCat J R').obj (L.complex.X n).val.presheaf
    (fun U => L.liftModule n U) (fun _ _ f s x => L.liftSMul_naturality n f s x)
  isSheaf := (L.complex.X n).isSheaf

/-- A section `s` of `R'` acts on the degree-`n` piece of `L♯` as `liftSMul`. -/
theorem liftPiece_smul (n : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R').obj.obj U)
    (x : (L.liftPiece n).val.obj U) :
    s • x = L.liftSMul n U s x :=
  rfl

/-- The differential of `L♯`: the differential of `L`, which is `R'`-linear. -/
noncomputable def liftD (i j : ℤ) : L.liftPiece i ⟶ L.liftPiece j :=
  ⟨PresheafOfModules.homMk (M₁ := (L.liftPiece i).val) (M₂ := (L.liftPiece j).val)
    ((PresheafOfModules.toPresheaf (toRingCat J R).obj).map (L.complex.d i j).val)
    (fun U s x => L.d_liftSMul i j U s x)⟩

/-- The differential of `L♯` is, on sections, the differential of `L`. -/
theorem liftD_val_app (i j : ℤ) (U : Cᵒᵖ) (x : (L.liftPiece i).val.obj U) :
    (L.liftD i j).val.app U x = (L.complex.d i j).val.app U x :=
  rfl

/-- **The complex of `L♯`.** -/
noncomputable def liftComplex : CochainComplex (SheafOfModules.{m} (toRingCat J R')) ℤ where
  X n := L.liftPiece n
  d i j := L.liftD i j
  shape i j hij := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => by
      change (L.complex.d i j).val.app U x = 0
      rw [L.complex.shape i j hij]
      rfl))
  d_comp_d' i j k _ _ := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => by
      change (L.complex.d j k).val.app U ((L.complex.d i j).val.app U x) = 0
      exact (congrArg (fun g => g.val.app U x) (L.complex.d_comp_d i j k)).trans rfl))

/-- **The lift `L♯` of a right differential graded `B♭`-module to a right differential graded
`B`-module**: the same sheaves of abelian groups, differentials and action, a section `s` of
`R'` acting as right multiplication by `s · 1`. -/
noncomputable def liftCoeff : DifferentialGradedModule.{t, a, m} B where
  complex := L.liftComplex
  mul n i :=
    { app := fun U => (L.mul n i).app U
      map_smul_left := fun U s x b => eq_of_heq ((mul_liftSMul_heq (L := L) n i U s x b).trans
        (liftSMul_mul_heq (L := L) n i U s x b).symm)
      map_smul_right := fun U s x b => eq_of_heq (liftSMul_mul_heq (L := L) n i U s x b).symm
      naturality := fun f x y => (L.mul n i).naturality f x y }
  mul_assoc := L.mul_assoc
  mul_one := L.mul_one
  leibniz := L.leibniz

/-- In a right differential graded module, right multiplication by `s · 1` is the action of `s`,
up to the cast along `n + 0 = n`. -/
private theorem gradedCast_mul_smul_one {R₀ : Sheaf J CommRingCat.{t}}
    {B₀ : DifferentialGradedAlgebra.{t, a} (toRingCat J R₀)}
    (Q : DifferentialGradedModule.{t, a, m} B₀) (n : ℤ) (U : Cᵒᵖ) (s : (toRingCat J R₀).obj.obj U)
    (y : (Q.complex.X n).val.obj U) :
    gradedCast (fun q ↦ (Q.complex.X q).val.obj U) (add_zero n)
      ((Q.mul n 0).app U y (s • B₀.one.eval U)) = s • y := by
  rw [(Q.mul n 0).map_smul_right, gradedCast_smul]
  exact congrArg (fun z => s • z) (eq_of_heq ((gradedCast_heq _ _ _).trans (Q.mul_one n U y)))

/-- The action of a section of `R` on `L` through `α` is its original action. -/
theorem liftSMul_algebraMap (n : ℤ) (U : Cᵒᵖ) (r : (toRingCat J R).obj.obj U)
    (x : (L.complex.X n).val.obj U) :
    L.liftSMul n U ((toRingCatHom α).hom.app U r) x = r • x := by
  unfold liftSMul
  exact gradedCast_mul_smul_one L n U r x

/-- The comparison of the restriction of a piece of `L♯` with the piece of `L`. -/
noncomputable def restrictLiftPieceIso (n : ℤ) :
    (restrictCoeffSheaf α).obj (L.liftPiece n) ≅ L.complex.X n where
  hom := ⟨PresheafOfModules.homMk (𝟙 (L.complex.X n).val.presheaf)
    (fun U r x => L.liftSMul_algebraMap n U r x)⟩
  inv := ⟨PresheafOfModules.homMk (M₂ := ((restrictCoeffSheaf α).obj (L.liftPiece n)).val)
    (𝟙 (L.complex.X n).val.presheaf) (fun U r x => (L.liftSMul_algebraMap n U r x).symm)⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

/-- **`L♯` restricts back to `L`**, as complexes of sheaves of `R`-modules: the comparison is the
identity of the underlying sheaves of abelian groups in each degree. -/
noncomputable def restrictLiftComplexIso :
    (L.liftCoeff.restrictCoeff (α := α)).complex ≅ L.complex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => L.restrictLiftPieceIso n)
    (fun _ _ _ => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
      ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)))

end Lift

/-! ### Morphisms out of a lift -/

section HomEquiv

variable (L : DifferentialGradedModule.{t, a, m} (B.restrictCoeff α))
  (Q : DifferentialGradedModule.{t, a, m} B)

/-- A morphism out of `L♯` read as a morphism out of `L`. -/
noncomputable def liftCoeffHomToFun (g : L.liftCoeff ⟶ Q) : L ⟶ Q.restrictCoeff :=
  Hom.mk (M := L) (N := Q.restrictCoeff)
    (HomologicalComplex.Hom.mk (A := L.complex) (B := Q.restrictCoeff.complex)
      (fun n => ⟨PresheafOfModules.homMk (M₁ := (L.complex.X n).val)
          (M₂ := (Q.restrictCoeff.complex.X n).val)
            ((PresheafOfModules.toPresheaf (toRingCat J R').obj).map
              (g.toHomologicalComplex.f n).val)
        (fun U r x => by
          change (g.toHomologicalComplex.f n).val.app U (r • x) =
            ((toRingCatHom α).hom.app U r) •
              @id ((Q.complex.X n).val.obj U) ((g.toHomologicalComplex.f n).val.app U x)
          rw [← L.liftSMul_algebraMap n U r x]
          exact (g.toHomologicalComplex.f n).val.app U |>.hom.map_smul _ _)⟩)
      (fun i j hij => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
        ModuleCat.hom_ext (LinearMap.ext fun x =>
          congrArg (fun φ => φ.val.app U x) (g.toHomologicalComplex.comm' i j hij)))))
    (fun n i U x y => g.map_mul n i U x y)

/-- In a right differential graded `B`-module, right multiplication by `s · 1` is the action
of `s`. -/
theorem mul_smul_one_eq (Q : DifferentialGradedModule.{t, a, m} B) (n : ℤ) (U : Cᵒᵖ)
    (s : (toRingCat J R').obj.obj U) (y : (Q.complex.X n).val.obj U) :
    gradedCast (fun q ↦ (Q.complex.X q).val.obj U) (add_zero n)
      ((Q.mul n 0).app U y (s • B.one.eval U)) = s • y :=
  gradedCast_mul_smul_one Q n U s y

/-- A morphism into a restriction commutes with the action of `R'`. -/
theorem hom_liftSMul (h : L ⟶ Q.restrictCoeff) (n : ℤ) (U : Cᵒᵖ)
    (s : (toRingCat J R').obj.obj U) (x : (L.complex.X n).val.obj U) :
    (h.toHomologicalComplex.f n).val.app U (L.liftSMul n U s x) =
      s • @id ((Q.complex.X n).val.obj U) ((h.toHomologicalComplex.f n).val.app U x) := by
  unfold liftSMul
  rw [gradedCast_hom_f_app h.toHomologicalComplex (add_zero n) U, h.map_mul n 0 U x]
  exact mul_smul_one_eq Q n U s _

/-- A morphism out of `L` into a restriction read as a morphism out of `L♯`. -/
noncomputable def liftCoeffHomInvFun (h : L ⟶ Q.restrictCoeff) : L.liftCoeff ⟶ Q :=
  Hom.mk (M := L.liftCoeff) (N := Q)
    (HomologicalComplex.Hom.mk (A := L.liftCoeff.complex) (B := Q.complex)
      (fun n => ⟨PresheafOfModules.homMk (M₁ := (L.liftPiece n).val) (M₂ := (Q.complex.X n).val)
            ((PresheafOfModules.toPresheaf (toRingCat J R).obj).map
              (h.toHomologicalComplex.f n).val)
        (fun U s x => hom_liftSMul L Q h n U s x)⟩)
      (fun i j hij => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
        ModuleCat.hom_ext (LinearMap.ext fun x =>
          congrArg (fun φ => φ.val.app U x) (h.toHomologicalComplex.comm' i j hij)))))
    (fun n i U x y => h.map_mul n i U x y)

/-- **Morphisms out of `L♯` are the morphisms out of `L` into restrictions.** -/
noncomputable def liftCoeffHomEquiv : (L.liftCoeff ⟶ Q) ≃ (L ⟶ Q.restrictCoeff) where
  toFun := liftCoeffHomToFun L Q
  invFun := liftCoeffHomInvFun L Q
  left_inv _ := rfl
  right_inv _ := Hom.ext fun _ => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- The bijection is natural in the target. -/
theorem liftCoeffHomEquiv_comp {Q Q' : DifferentialGradedModule.{t, a, m} B}
    (g : L.liftCoeff ⟶ Q) (k : Q ⟶ Q') :
    liftCoeffHomEquiv L Q' (g ≫ k) =
      liftCoeffHomEquiv L Q g ≫ (restrictCoeffFunctor α).map k :=
  Hom.ext fun _ => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- **`L♯` corepresents the functor corepresented by `L`, precomposed with restriction of
scalars.** -/
noncomputable def liftCoeffCorepresentableBy
    {F : DifferentialGradedModule.{t, a, m} (B.restrictCoeff α) ⥤ Type*}
    (e : F.CorepresentableBy L) :
    (restrictCoeffFunctor α ⋙ F).CorepresentableBy L.liftCoeff where
  homEquiv {Q} := (liftCoeffHomEquiv L Q).trans e.homEquiv
  homEquiv_comp {Q Q'} k g :=
    (congrArg (fun z : L ⟶ (restrictCoeffFunctor α).obj Q' => e.homEquiv z)
      (liftCoeffHomEquiv_comp L g k)).trans
      (e.homEquiv_comp ((restrictCoeffFunctor α).map k) (liftCoeffHomEquiv L Q g))

end HomEquiv

/-! ### Acyclicity across the lift -/

section Acyclic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {R R' : Sheaf J CommRingCat.{t}} {α : toRingCat J R ⟶ toRingCat J R'}
  {B : DifferentialGradedAlgebra.{t, a} (toRingCat J R')}

/-- **A complex of sheaves of `R'`-modules is acyclic as soon as its restriction of scalars
is**: restriction of scalars is exact and faithful. -/
theorem _root_.SheafOfModules.acyclic_of_acyclic_coeffRestrict
    (K : CochainComplex (SheafOfModules.{t} (toRingCat J R')) ℤ)
    (h : (((restrictCoeffSheaf α).mapHomologicalComplex _).obj K).Acyclic) : K.Acyclic := by
  obtain ⟨_, _⟩ := Stacks.SheafOfModules.ChangeOfRings.exactFunctor_restrictScalars
    (toRingCatHom α)
  exact fun i => (ShortComplex.exact_map_iff_of_faithful (K.sc i) (restrictCoeffSheaf α)).mp (h i)

/-- **Acyclicity transfers along the lift**: if `L` corepresents a functor `F` and `T`
corepresents `F` precomposed with restriction of scalars, then `T` is acyclic as soon as `L`
is, `T` being the lift `L♯`. -/
theorem acyclic_of_corepresentableBy_restrictCoeff
    {F : DifferentialGradedModule.{t, a, t} (B.restrictCoeff α) ⥤ Type*}
    {L : DifferentialGradedModule.{t, a, t} (B.restrictCoeff α)} (eL : F.CorepresentableBy L)
    {T : DifferentialGradedModule.{t, a, t} B}
    (eT : (restrictCoeffFunctor α ⋙ F).CorepresentableBy T) (hL : L.complex.Acyclic) :
    T.complex.Acyclic := by
  let iso : L.liftCoeff ≅ T := (liftCoeffCorepresentableBy L eL).uniqueUpToIso eT
  have hlift : L.liftCoeff.complex.Acyclic :=
    _root_.SheafOfModules.acyclic_of_acyclic_coeffRestrict (α := α) _
      fun i => (hL i).of_iso L.restrictLiftComplexIso.symm
  have e' : L.liftCoeff.complex ≅ T.complex :=
    { hom := iso.hom.toHomologicalComplex
      inv := iso.inv.toHomologicalComplex
      hom_inv_id := congrArg Hom.toHomologicalComplex iso.hom_inv_id
      inv_hom_id := congrArg Hom.toHomologicalComplex iso.inv_hom_id }
  exact fun i => (hlift i).of_iso e'

end Acyclic

end DifferentialGradedModule

end SheafOfModules

end
