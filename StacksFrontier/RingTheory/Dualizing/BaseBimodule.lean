module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.RingTheory.Dualizing.DifferentialGradedResolution

/-!
# Every right differential graded module is a bimodule over the base ring

Let `R` be a commutative ring and `(B, d)` a differential graded `R`-algebra. The base ring
placed in degree zero with zero differential, `Dualizing.baseAlgebra R`, is the unit of the
differential graded world, and this file records the corresponding statement about modules: a
right differential graded `B`-module is a differential graded `(R, B)`-bimodule in exactly one
way, the left action being scalar multiplication by `R`. "Exactly one" is literal: the left action
is not merely canonical but forced, so a bimodule over the base ring carries no information beyond
its right module and the two notions are *equal*, not just equivalent.

Specialised to `B = A` placed in degree zero, and composed with the equivalence
`DifferentialGradedModule.degreeZeroEquivalence` between differential graded modules over `A` in
degree zero and cochain complexes of `A`-modules, this turns an ordinary complex of `A`-modules
into a differential graded `(R, A)`-bimodule.

## Main definitions

* `Dualizing.baseLeftAction` — **the scalar left action of the base ring in degree zero on an
  arbitrary cochain complex of `R`-modules.**
* `Dualizing.baseBimodule` — **a right differential graded `B`-module, regarded as a differential
  graded `(R, B)`-bimodule.**
* `Dualizing.baseBimoduleHom` — the same on homomorphisms: a homomorphism of right `B`-modules is
  automatically a homomorphism of the attached bimodules.
* `Dualizing.complexBimodule` — **an ordinary cochain complex of `A`-modules, regarded as a
  differential graded `(R, A)`-bimodule**, and `Dualizing.complexBimoduleHom` on morphisms.

## Main results

* `Dualizing.baseLeftAction_v_coe` — the scalar action evaluated on a homogeneous element: in
  every degree it is multiplication by the scalar. This single formula covers all degrees,
  because a homogeneous element of nonzero degree of `Dualizing.baseAlgebra R` is zero.
* `Dualizing.isRightLinearCochain_baseLeftAction` — every homogeneous piece of the scalar action
  is right `B`-linear, which is what makes it a bimodule structure.
* `Dualizing.baseLeftAction_unique` — **the scalar action is the only left action of the base ring
  in degree zero**, and `Dualizing.bimodule_eq_baseBimodule` — **every differential graded
  `(R, B)`-bimodule is the one attached to its right module.** Consequently
  `Dualizing.derivedTensorFunctor_eq_baseBimodule`: the derived tensor product of Stacks 09LS with
  a bimodule over the base ring depends only on its right module. In particular the left
  `R`-action used in tensoring over the base ring is always the one induced by the structure
  homomorphism — for every bimodule, with no hypothesis, since there is no other action available.
* `Dualizing.complexBimoduleRightModuleIso` — the right module of the bimodule attached to a
  complex is that complex, read through the degree-zero equivalence.

## Implementation notes

The left action is not written out by hand. Left differential graded actions of `A` on a complex
`M`, recorded as cochains, correspond to homomorphisms of differential graded algebras from `A`
into the endomorphism algebra of `M` (`DifferentialGradedAlgebra.leftActionEquivHom`, the
cochain-level form of Tag 0FQ3, whose module statement is
`DifferentialGraded.LeftModule.toEndomorphismHom_spec_surjective_eq_iff`), and
`Dualizing.baseHom` already provides such a homomorphism out of `Dualizing.baseAlgebra R` for
*every* differential graded algebra, the endomorphism algebra included. So the action is obtained
by transporting `Dualizing.baseHom` through that correspondence, and the only thing left to prove
is the formula for its homogeneous pieces, which comes from `R`-linearity of the correspondence
together with the fact that the unit goes to the identity cochain.

The grading of `Dualizing.baseAlgebra R` is all of `R` in degree zero and trivial elsewhere, so a
homogeneous element of nonzero degree vanishes. That is why `Dualizing.baseLeftAction_v_coe` can
be stated uniformly in the degree: in a nonzero degree both sides are zero. It is stated at an
arbitrary target index with a proof of `p + n = q`, rather than at `p + n`, because `p + 0` is not
syntactically `p` for a variable `p`, so that the formula applies at whichever index is at hand.

Both the differential graded algebras and their modules live in a single universe, which is the
encoding of the differential graded chapter in this tree (Tag 09JJ).

## References

* [Stacks Project, Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI), bimodules as a right
  module with a compatible left action.
* [Stacks Project, Tag 0FQ3](https://stacks.math.columbia.edu/tag/0FQ3), left actions as
  homomorphisms into the endomorphism algebra.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex DifferentialGraded
  DifferentialGradedModule

universe u

namespace Dualizing

variable {R : Type u} [CommRing R]

/-! ### The scalar left action of the base ring -/

/-- The identity cochain of degree zero, evaluated on a homogeneous element at an arbitrary
target index: it is the element itself. -/
private theorem ofHom_id_v_coe (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) (p q : ℤ) (h : p + 0 = q) (x : M.grading p) :
    ((show M.grading q from ((Cochain.ofHom (𝟙 M.toCochainComplex)).v p q h) x) : M.M) =
      (x : M.M) := by
  obtain rfl : p = q := by omega
  rw [Cochain.ofHom_v]
  rfl

/-- **The canonical left action of the base ring in degree zero on an arbitrary complex of
`R`-modules.** A scalar acts by scalar multiplication; the action is obtained by transporting
`Dualizing.baseHom` into the endomorphism algebra through `leftActionEquivHom`, the cochain-level
form of Tag 0FQ3. -/
def baseLeftAction (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (baseAlgebra R).LeftAction M :=
  (DifferentialGradedAlgebra.leftActionEquivHom (baseAlgebra R) M).1.symm
    (baseHom (endomorphismDGA M).algebra)

/-- In degree zero the scalar action is the scalar multiple of the identity cochain. -/
theorem baseLeftAction_action_zero (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (a : (baseAlgebra R).grading 0) :
    (baseLeftAction M).action 0 a = (a : R) • Cochain.ofHom (𝟙 M) := by
  have hhom : (DifferentialGradedAlgebra.leftActionEquivHom (baseAlgebra R) M).1
      (baseLeftAction M) = baseHom (endomorphismDGA M).algebra :=
    (DifferentialGradedAlgebra.leftActionEquivHom (baseAlgebra R) M).1.apply_symm_apply _
  rw [← (DifferentialGradedAlgebra.leftActionEquivHom (baseAlgebra R) M).2
    (baseLeftAction M) 0 a]
  generalize_proofs p1 p2 p3 p4
  have hv : ((DifferentialGradedAlgebra.leftActionEquivHom (baseAlgebra R) M).1
      (baseLeftAction M)).toAlgebraHom (a : R) =
      (a : R) • (1 : (endomorphismDGA M).algebra.A) := by
    rw [congrArg (fun ψ => DifferentialGradedAlgebra.Hom.toAlgebraHom ψ (a : R)) hhom]
    change (algebraMap R (endomorphismDGA M).algebra.A) (a : R) = _
    rw [Algebra.algebraMap_eq_smul_one]
  rw [show (⟨_, p3⟩ : (endomorphismDGA M).algebra.grading 0) =
      (a : R) • ⟨1, SetLike.one_mem_graded (endomorphismDGA M).algebra.grading⟩ from
    Subtype.ext hv, map_smul, (endomorphismDGA M).map_one]

/-- A homogeneous element of nonzero degree of `Dualizing.baseAlgebra R` is zero. -/
private theorem baseAlgebra_grading_eq_zero {n : ℤ} (hn : n ≠ 0) (a : (baseAlgebra R).grading n) :
    a = 0 := by
  ext; simpa [DifferentialGradedAlgebra.degreeZeroGrading, hn] using a.property

/-- Outside degree zero the scalar action vanishes, the grading of `Dualizing.baseAlgebra R`
being trivial there. -/
theorem baseLeftAction_action_of_ne (M : CochainComplex (ModuleCat.{u} R) ℤ) {n : ℤ} (hn : n ≠ 0)
    (a : (baseAlgebra R).grading n) : (baseLeftAction M).action n a = 0 := by
  rw [baseAlgebra_grading_eq_zero hn a, map_zero]

/-- **The scalar action evaluated on a homogeneous element: it is multiplication by the
scalar.** One formula for every degree, since a homogeneous element of nonzero degree of
`Dualizing.baseAlgebra R` is zero and both sides then vanish. -/
theorem baseLeftAction_v_coe (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) {n : ℤ} (a : (baseAlgebra R).grading n)
    (p q : ℤ) (h : p + n = q) (x : M.grading p) :
    ((show M.grading q from
        ((baseLeftAction M.toCochainComplex).action n a).v p q h x) : M.M) =
      (a : R) • (x : M.M) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [baseLeftAction_action_zero, Cochain.smul_v]
    change (a : R) • ((show M.grading q from
      ((Cochain.ofHom (𝟙 M.toCochainComplex)).v p q h) x : M.M)) = _
    rw [ofHom_id_v_coe]
  · rw [baseLeftAction_action_of_ne _ hn, Cochain.zero_v, baseAlgebra_grading_eq_zero hn a]
    change (0 : M.M) = _
    rw [ZeroMemClass.coe_zero, zero_smul]

/-! ### The bimodule attached to a right module -/

/-- A scalar multiple of a right `B`-linear cochain is right `B`-linear. -/
private theorem isRightLinear_smul (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) {n : ℤ} (a : R)
    (f : Cochain M.toCochainComplex M.toCochainComplex n)
    (hf : IsRightLinearCochain B M f) : IsRightLinearCochain B M (a • f) := by
  obtain ⟨g, hg⟩ := hf
  refine ⟨a • g, fun p x => ?_⟩
  rw [Cochain.smul_v]
  change a • ((show M.grading (p + n) from (f.v p (p + n) rfl) x : M.M)) = _
  rw [hg p x]
  rfl

/-- The identity cochain is right `B`-linear. -/
private theorem isRightLinear_ofHom_id (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) :
    IsRightLinearCochain B M (Cochain.ofHom (𝟙 M.toCochainComplex)) :=
  ⟨homogeneousMapId B M, fun p x => by
    rw [ofHom_id_v_coe B M p (p + 0) rfl x]
    rfl⟩

/-- The zero cochain is right `B`-linear. -/
private theorem isRightLinear_zero (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) (n : ℤ) :
    IsRightLinearCochain B M (0 : Cochain M.toCochainComplex M.toCochainComplex n) :=
  ⟨0, fun p x => by
    rw [Cochain.zero_v]
    rfl⟩

/-- **Every homogeneous piece of the scalar action is right `B`-linear.** In degree zero it is a
scalar multiple of the identity, and in every other degree it is zero. -/
theorem isRightLinearCochain_baseLeftAction (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) (n : ℤ) (a : (baseAlgebra R).grading n) :
    IsRightLinearCochain B M ((baseLeftAction M.toCochainComplex).action n a) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [baseLeftAction_action_zero]
    exact isRightLinear_smul B M _ _ (isRightLinear_ofHom_id B M)
  · rw [baseLeftAction_action_of_ne _ hn]
    exact isRightLinear_zero B M n

/-- The scalar action, as a differential graded bimodule structure over the base ring. -/
def baseBimoduleStructure (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) : BimoduleStructure (baseAlgebra R) B M :=
  ⟨baseLeftAction M.toCochainComplex, isRightLinearCochain_baseLeftAction B M⟩

/-- **A right differential graded `B`-module, regarded as a differential graded
`(R, B)`-bimodule**, the left action being scalar multiplication by the base ring. -/
def baseBimodule (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) : Bimodule (baseAlgebra R) B where
  rightModule := M
  leftAction := baseBimoduleStructure B M

/-- The right module of `Dualizing.baseBimodule B M` is `M`. -/
@[simp] theorem baseBimodule_rightModule (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) : (baseBimodule B M).rightModule = M := rfl

/-- `Dualizing.baseLeftAction_v_coe`, restated at the left action of
`Dualizing.baseBimodule` itself. -/
theorem baseBimodule_leftAction_v_coe (B : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule B) {n : ℤ} (a : (baseAlgebra R).grading n)
    (p q : ℤ) (h : p + n = q) (x : (baseBimodule B M).rightModule.grading p) :
    ((show (baseBimodule B M).rightModule.grading q from
        ((baseBimodule B M).leftAction.1.action n a).v p q h x) :
      (baseBimodule B M).rightModule.M) =
      (a : R) • ((x : (baseBimodule B M).rightModule.grading p) :
        (baseBimodule B M).rightModule.M) :=
  baseLeftAction_v_coe B M a p q h x

/-- **A homomorphism of right `B`-modules is a homomorphism of the attached bimodules.** The left
action is scalar multiplication and a homomorphism of differential graded modules is `R`-linear,
so there is nothing to impose. -/
def baseBimoduleHom (B : DifferentialGradedAlgebra.{u, u} R)
    {M N : DifferentialGradedModule B} (f : M ⟶ N) :
    baseBimodule B M ⟶ baseBimodule B N where
  rightHom := f
  map_left n p a x := by
    rw [baseBimodule_leftAction_v_coe B M a p (p + n) rfl x]
    refine Eq.trans ?_ (baseBimodule_leftAction_v_coe B N a p (p + n) rfl (f.gradedMap p x)).symm
    rw [map_smul]
    rfl

/-- The underlying homomorphism of right modules of `Dualizing.baseBimoduleHom B f` is `f`. -/
@[simp] theorem baseBimoduleHom_rightHom (B : DifferentialGradedAlgebra.{u, u} R)
    {M N : DifferentialGradedModule B} (f : M ⟶ N) :
    (baseBimoduleHom B f).rightHom = f := rfl

/-! ### The scalar action is the only one -/

/-- **The scalar action is the only left action of the base ring in degree zero.** The action map
in each degree is `R`-linear and the unit acts as the identity, so a degree-zero homogeneous
element `a` acts as `a • 1`; in a nonzero degree the only homogeneous element is zero. -/
theorem baseLeftAction_unique (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (L : (baseAlgebra R).LeftAction M) : L = baseLeftAction M := by
  refine DifferentialGradedAlgebra.LeftAction.ext_action fun n a => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have ha : ((a : R) • ⟨1, SetLike.one_mem_graded (baseAlgebra R).grading⟩ :
        (baseAlgebra R).grading 0) = a := by
      refine Subtype.ext ?_
      change (a : R) • (1 : R) = (a : R)
      rw [smul_eq_mul, mul_one]
    calc (L.action 0) a = (L.action 0) ((a : R) • ⟨1, _⟩) := by rw [ha]
      _ = (a : R) • (L.action 0) ⟨1, _⟩ := map_smul _ _ _
      _ = (a : R) • Cochain.ofHom (𝟙 M) := by rw [L.map_one]
      _ = (baseLeftAction M).action 0 a := (baseLeftAction_action_zero M a).symm
  · rw [baseLeftAction_action_of_ne _ hn, baseAlgebra_grading_eq_zero hn a, map_zero]

/-- **Every differential graded `(R, B)`-bimodule is the one attached to its right module.** A
bimodule over the base ring in degree zero carries no information beyond its right module: the
left action is forced to be scalar multiplication by `Dualizing.baseLeftAction_unique`.

This is an equality of bimodules, not merely an isomorphism, so it may be transported through any
construction by `congrArg`. In particular the left `R`-action used when tensoring over the base
ring is always the one induced by the structure homomorphism, for *every* bimodule — there is no
room for it to be anything else. -/
theorem bimodule_eq_baseBimodule (B : DifferentialGradedAlgebra.{u, u} R)
    (N : Bimodule (baseAlgebra R) B) : N = baseBimodule B N.rightModule := by
  obtain ⟨M, L⟩ := N
  exact congrArg (Bimodule.mk M) (Subtype.ext (baseLeftAction_unique M.toCochainComplex L.1))

/-- **The derived tensor product with a bimodule over the base ring depends only on its right
module.** An immediate consequence of `Dualizing.bimodule_eq_baseBimodule`. -/
theorem derivedTensorFunctor_eq_baseBimodule (B : DifferentialGradedAlgebra.{u, u} R)
    (N : Bimodule (baseAlgebra R) B) :
    Bimodule.derivedTensorFunctor N =
      Bimodule.derivedTensorFunctor (baseBimodule B N.rightModule) :=
  congrArg Bimodule.derivedTensorFunctor (bimodule_eq_baseBimodule B N)

/-! ### An ordinary complex as a bimodule -/

section DegreeZero

variable (R) (A : Type u) [CommRing A] [Algebra R A]

/-- **An ordinary cochain complex of `A`-modules, regarded as a differential graded
`(R, A)`-bimodule.** The complex is read as a differential graded module over `A` placed in
degree zero through `DifferentialGradedModule.degreeZeroEquivalence`, and the left `R`-action is
scalar multiplication. -/
def complexBimodule (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    Bimodule (baseAlgebra R) (DifferentialGradedAlgebra.degreeZero R A) :=
  baseBimodule _ ((degreeZeroEquivalence (R := R) (A := A)).inverse.obj N)

/-- The right module of `Dualizing.complexBimodule R A N` is the differential graded module
attached to `N` by the degree-zero equivalence. -/
@[simp] theorem complexBimodule_rightModule (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    (complexBimodule R A N).rightModule =
      (degreeZeroEquivalence (R := R) (A := A)).inverse.obj N := rfl

/-- The right module of the bimodule attached to a complex is that complex, read through the
degree-zero equivalence. -/
def complexBimoduleRightModuleIso (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    (degreeZeroEquivalence (R := R) (A := A)).functor.obj
        (complexBimodule R A N).rightModule ≅ N :=
  (degreeZeroEquivalence (R := R) (A := A)).counitIso.app N

variable {A}

/-- A morphism of complexes of `A`-modules is a morphism of the attached bimodules. -/
def complexBimoduleHom {N N' : CochainComplex (ModuleCat.{u} A) ℤ} (r : N ⟶ N') :
    complexBimodule R A N ⟶ complexBimodule R A N' :=
  baseBimoduleHom _ ((degreeZeroEquivalence (R := R) (A := A)).inverse.map r)

/-- The underlying homomorphism of right modules of `Dualizing.complexBimoduleHom R r` is the
image of `r` under the degree-zero equivalence. -/
@[simp] theorem complexBimoduleHom_rightHom {N N' : CochainComplex (ModuleCat.{u} A) ℤ}
    (r : N ⟶ N') :
    (complexBimoduleHom R r).rightHom =
      (degreeZeroEquivalence (R := R) (A := A)).inverse.map r := rfl

end DegreeZero

end Dualizing

end
