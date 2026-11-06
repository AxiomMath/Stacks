module

public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.CategoryTheory.Center.QuotientLocalization
public import Mathlib.CategoryTheory.Center.Linear

/-!
# Central closed elements of degree zero act on differential graded modules

Let `(E, d)` be a differential graded algebra and `c ∈ E` a central element of degree zero with
`d c = 0`. Right multiplication by `c` is then an endomorphism `m ↦ m c` of every differential
graded `E`-module (it is `E`-linear because `c` is central, preserves degrees because `c` has
degree zero, and commutes with the differential by the Leibniz rule because `d c = 0`), and these
endomorphisms are natural: they form an element of the center of `Mod_(E, d)`. They descend to
the homotopy category `K(E, d)` and to the derived category `D(E, d)`.

A ring morphism `ψ : S →+* E` whose values are central, closed and of degree zero therefore makes
`D(E, d)` an `S`-linear category, the scalar `s` acting by right multiplication by `ψ s`.

## Main definitions

* `DifferentialGradedModule.IsCentralCocycle`: `c` is central, of degree zero, and closed.
* `DifferentialGradedModule.centralSMul`: right multiplication by such a `c`, as an endomorphism
  of a differential graded module.
* `DifferentialGradedModule.centralSMulCenter`: the corresponding element of the center of
  `Mod_(E, d)`.
* `DifferentialGradedModule.centerRingHom`, `DifferentialGradedModule.homotopyCenterRingHom`,
  `DifferentialGradedModule.derivedCenterRingHom`: a ring morphism `S →+* E` with central closed
  degree-zero values, read in the centers of `Mod_(E, d)`, `K(E, d)` and `D(E, d)`.
* `DifferentialGradedModule.derivedLinearOfCentral`: the resulting `S`-linear structure on
  `D(E, d)`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {E : DifferentialGradedAlgebra.{u, v} R}

/-- An element of a differential graded algebra that is central, of degree zero and closed. -/
structure IsCentralCocycle (c : E.A) : Prop where
  comm : ∀ b : E.A, c * b = b * c
  mem : c ∈ E.grading 0
  d_eq : E.d c = 0

variable {c : E.A} (hc : IsCentralCocycle c)

/-- **Right multiplication by a central closed element of degree zero** is an endomorphism of
every differential graded module. -/
def centralSMul (M : DifferentialGradedModule.{u, v, w} E) : M ⟶ M where
  toFun :=
    { toFun := fun x => MulOpposite.op c • x
      map_add' := smul_add _
      map_smul' := fun r x => smul_comm (MulOpposite.op c) r x }
  map_smul x a := by
    change MulOpposite.op c • MulOpposite.op a • x = MulOpposite.op a • MulOpposite.op c • x
    rw [smul_smul, smul_smul, ← MulOpposite.op_mul, ← MulOpposite.op_mul, hc.comm a]
  map_grading n x hx := by
    have h := M.smul_mem n 0 x c hx hc.mem
    rw [add_zero] at h
    exact h
  map_d := by
    refine LinearMap.ext fun x => ?_
    change MulOpposite.op c • M.d x = M.d (MulOpposite.op c • x)
    refine DirectSum.Decomposition.inductionOn M.grading (by simp) (fun {i} y => ?_)
      (fun y y' hy hy' => by rw [map_add, smul_add, hy, hy', smul_add, map_add]) x
    rw [M.leibniz i 0 y c y.2 hc.mem, hc.d_eq, MulOpposite.op_zero, zero_smul, smul_zero,
      add_zero]

/-- The endomorphism `centralSMul hc M` sends `x` to `x c`. -/
@[simp]
lemma centralSMul_toFun_apply (M : DifferentialGradedModule.{u, v, w} E) (x : M.M) :
    (centralSMul hc M).toFun x = MulOpposite.op c • x :=
  rfl

/-- Right multiplication by a central closed element of degree zero, as an element of the center
of `Mod_(E, d)`. -/
def centralSMulCenter : CatCenter (DifferentialGradedModule.{u, v, w} E) :=
  .of
  { app M := centralSMul hc M
    naturality M N f := by
      refine Hom.ext (LinearMap.ext fun x => ?_)
      exact (f.map_smul x c).symm }

/-- The component of `centralSMulCenter hc` at `M` is `centralSMul hc M`. -/
@[simp]
lemma centralSMulCenter_app (M : DifferentialGradedModule.{u, v, w} E) :
    (centralSMulCenter.{u, v, w} hc).app M = centralSMul hc M :=
  rfl

variable {S : Type*} [Ring S] (ψ : S →+* E.A) (hψ : ∀ s, IsCentralCocycle (ψ s))

/-- A ring morphism into a differential graded algebra whose values are central, closed and of
degree zero, read in the center of `Mod_(E, d)`: `s` acts by right multiplication by `ψ s`. -/
def centerRingHom : S →+* CatCenter (DifferentialGradedModule.{u, v, w} E) where
  toFun s := centralSMulCenter (hψ s)
  map_one' := CatCenter.ext _ _ fun M => Hom.ext (LinearMap.ext fun x => by
    change MulOpposite.op (ψ 1) • x = x
    rw [map_one, MulOpposite.op_one, one_smul])
  map_mul' s t := CatCenter.ext _ _ fun M => Hom.ext (LinearMap.ext fun x => by
    change MulOpposite.op (ψ (s * t)) • x =
      MulOpposite.op (ψ s) • MulOpposite.op (ψ t) • x
    rw [smul_smul, ← MulOpposite.op_mul, map_mul, (hψ s).comm])
  map_zero' := CatCenter.ext _ _ fun M => Hom.ext (LinearMap.ext fun x => by
    change MulOpposite.op (ψ 0) • x = 0
    rw [map_zero, MulOpposite.op_zero, zero_smul])
  map_add' s t := CatCenter.ext _ _ fun M => Hom.ext (LinearMap.ext fun x => by
    change MulOpposite.op (ψ (s + t)) • x =
      MulOpposite.op (ψ s) • x + MulOpposite.op (ψ t) • x
    rw [map_add, MulOpposite.op_add, add_smul])

/-- The component of `centerRingHom ψ hψ s` at `M` is right multiplication by `ψ s`. -/
@[simp]
lemma centerRingHom_app (s : S) (M : DifferentialGradedModule.{u, v, w} E) :
    (centerRingHom.{u, v, w} ψ hψ s).app M = centralSMul (hψ s) M :=
  rfl

/-- The same ring morphism, read in the center of the homotopy category `K(E, d)`. -/
def homotopyCenterRingHom : S →+* CatCenter (HomotopyCategory.{u, v, w} E) :=
  (CatCenter.quotientRingHom (homotopyRel E)).comp (centerRingHom.{u, v, w} ψ hψ)

/-- The component of `homotopyCenterRingHom ψ hψ s` at the image of `M` in `K(E, d)` is the image
of right multiplication by `ψ s`. -/
@[simp]
lemma homotopyCenterRingHom_app (s : S) (M : DifferentialGradedModule.{u, v, w} E) :
    (homotopyCenterRingHom.{u, v, w} ψ hψ s).app ((toHomotopyCategory E).obj M) =
      (toHomotopyCategory E).map (centralSMul (hψ s) M) :=
  rfl

/-- The same ring morphism, read in the center of the derived category `D(E, d)`. -/
def derivedCenterRingHom : S →+* CatCenter (derivedCategory.{u, v, w} E) :=
  (CatCenter.localizationRingHom (quasiIsomorphisms.{u, v, w} E).Q
    (quasiIsomorphisms.{u, v, w} E)).comp (homotopyCenterRingHom.{u, v, w} ψ hψ)

/-- The component of `derivedCenterRingHom ψ hψ s` at the image of `X` in `D(E, d)` is the image
of the component of `homotopyCenterRingHom ψ hψ s` at `X`. -/
lemma derivedCenterRingHom_app (s : S) (X : HomotopyCategory.{u, v, w} E) :
    (derivedCenterRingHom.{u, v, w} ψ hψ s).app ((quasiIsomorphisms.{u, v, w} E).Q.obj X) =
      (quasiIsomorphisms.{u, v, w} E).Q.map ((homotopyCenterRingHom.{u, v, w} ψ hψ s).app X) :=
  CatCenter.localization_app _ _ _ X

/-- **`D(E, d)` is linear over a ring mapping to the central closed elements of degree zero**,
a scalar `s` acting on `M` by right multiplication by `ψ s`. -/
@[instance_reducible]
def derivedLinearOfCentral : Linear S (derivedCategory.{u, v, w} E) :=
  Linear.ofRingMorphism (derivedCenterRingHom.{u, v, w} ψ hψ)

end DifferentialGradedModule
