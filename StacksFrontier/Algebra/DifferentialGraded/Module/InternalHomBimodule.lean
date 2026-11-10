module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleComposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents

/-!
# The internal hom into the algebra as a bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `T`
be a differential graded `(A, B)`-bimodule. The internal hom
`S = Hom^•_B(T, B) = Hom_{Mod^{dg}_{(B, d)}}(T, B)`
is a right differential graded `A`-module, the algebra `A` acting by precomposition with its left
action on `T` (Tag 0FQR). Because `B` is itself a differential graded `(B, B)`-bimodule, `S`
carries in addition a *left* differential graded `B`-action: a homogeneous `b ∈ B^n` acts by
postcomposition with left multiplication by `b`, which is a homogeneous right-`B`-linear
endomorphism of `B`. This makes `S` a differential graded `(B, A)`-bimodule, which is the first
assertion of [Stacks, Tag 0BZ0].

The construction is the one of the source read through the internal hom functor of Tag 0FQQ: the
source obtains the two actions from the composition pairing
`Hom_B(T, B) ⊗ Hom_B(T, T) → Hom_B(T, B)` of Tag 09LC together with the maps `A → Hom_B(T, T)`
and `B → Hom_B(B, B)`. Here the right `A`-action is already part of `Hom^•_B(T, B)` (it *is* that
pairing with `A → Hom_B(T, T)`, built into Tag 0FQR), and the left `B`-action is the image of
left multiplication under the differential graded functor `Hom^•_B(T, -)` of Tag 0FQQ, which is
that pairing in its other variable.

Nothing is chosen: the action is the image of an explicit homogeneous endomorphism under an
already-constructed differential graded functor, and the three conditions defining a left
differential graded action are the functor's `map_id`, `map_comp` and `map_d`. Its right
`A`-linearity — the condition that makes it a bimodule structure — is automatic, the morphisms of
`dgCategory A` being the right `A`-linear maps.

*The structure is unconditional.* Tag 0BZ0 states this assertion under its hypotheses (1) that
`T` defines a compact object of `D(B, d)` and (2) that `S` represents `R\Hom(T, B)` in
`D(A, d)`. Neither is needed for the bimodule structure, and neither appears below; the tag
attribute on `DifferentialGraded.Bimodule.homDualBimodule` is therefore on a statement with no
hypothesis the source does not have.

*What this file does not cover.* The second assertion of Tag 0BZ0 — the isomorphism
`N ⊗_B^𝐋 S ⟶ R\Hom(T, N)` functorial in `N` — is **not** proved anywhere, and the clause string
of the tag attribute below says so. The undervied comparison `N ⊗_B S ⟶ Hom^•_B(T, N)` out of
which the source builds that map is
`StacksFrontier/Algebra/DifferentialGraded/Module/InternalHomTensorComparison.lean`, whose
implementation notes record exactly what remains.

**Not the graded character dual.** `DifferentialGraded.Bimodule.homDualModule` below is
`Hom^•_B(T, B)`, homomorphisms into the *algebra* `B`. It is unrelated to the graded character
dual `A^∨` of `StacksFrontier/Algebra/DifferentialGraded/Module/CharacterDual.lean`, which is
homomorphisms into the base ring.

## Main definitions

* `DifferentialGraded.Bimodule.regularBimodule`: a differential graded algebra as a differential
  graded bimodule over itself.
* `DifferentialGraded.Bimodule.homDualPresentation` and
  `DifferentialGraded.Bimodule.homDualModule`: the chosen presentation of `S = Hom^•_B(T, B)` and
  its underlying right differential graded `A`-module.
* `DifferentialGraded.Bimodule.homDualActionHomogeneous`: the action of a homogeneous element of
  `B` on `S`, as a homogeneous right-`A`-linear endomorphism of `S`.
* `DifferentialGraded.Bimodule.homDualLeftAction`: the resulting left differential graded
  `B`-action on the complex underlying `S`.
* `DifferentialGraded.Bimodule.homDualBimodule`: **the differential graded `(B, A)`-bimodule
  structure on `S` of Tag 0BZ0**.

## Main results

* `DifferentialGraded.Bimodule.leftMulRegular_apply`: left multiplication on the regular module
  is left multiplication.
* `DifferentialGraded.Bimodule.homDualSmul`: the action of a homogeneous element of `B` on a
  homogeneous element of `S`, in its graded piece.
* `DifferentialGraded.Bimodule.homDualBimodule_action_apply`: the homogeneous right-`B`-linear
  map `T → B` attached to `b · f` is `t ↦ b * f t`. This is the identification that says the
  structure constructed below is the one Tag 0BZ0 asks for.

## References

* [Stacks Project, Tag 0BZ0](https://stacks.math.columbia.edu/tag/0BZ0); the internal hom is
  [Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR), its functoriality
  [Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ), the composition pairing the source uses
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), and the regular bimodule
  [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX).
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex DifferentialGradedModule

namespace DifferentialGraded.Bimodule

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The regular bimodule -/

/-- A differential graded algebra as a differential graded bimodule over itself: the regular
right module with the left action by multiplication. -/
def regularBimodule (B : DifferentialGradedAlgebra.{u, u} R) : Bimodule B B where
  rightModule := regularModule B
  leftAction := regularBimoduleStructure B.idHom

/-- Left multiplication by a homogeneous element of `B` on the regular module, as a degree-`n`
homogeneous morphism `B ⟶ B` of the differential graded category of right differential graded
`B`-modules. -/
def leftMulRegular {n : ℤ} (b : B.grading n) :
    (dgCategory B).Hom (regularModule B) (regularModule B) n :=
  leftMulHomogeneous (regularBimodule B) b

/-- Left multiplication by a homogeneous element on the regular module is left
multiplication. -/
theorem leftMulRegular_apply {n : ℤ} (b : B.grading n) (y : B.A) :
    (leftMulRegular b).1 y = (b : B.A) * y := by
  change leftActionTotal B B (regularModule B) (regularBimoduleStructure B.idHom).1 (b : B.A) y =
    (b : B.A) * y
  rw [leftActionTotal_apply B B (regularModule B) (regularBimoduleStructure B.idHom).1 n b]
  induction y using DirectSum.Decomposition.inductionOn B.grading with
  | zero => rw [map_zero, mul_zero]
  | add y z hy hz => rw [map_add, hy, hz, mul_add]
  | @homogeneous q y =>
    rw [totalizeCochain_apply_of_eq B (regularModule B) n q (q + n) rfl _ y]
    exact (regularBimoduleStructure_action B.idHom n q b y).trans (by simp)

/-- Left multiplication on the regular module is additive in the multiplier. -/
theorem leftMulRegular_add {n : ℤ} (b c : B.grading n) :
    leftMulRegular (b + c) = leftMulRegular b + leftMulRegular c :=
  leftMulHomogeneous_add (regularBimodule B) b c

/-- Left multiplication on the regular module is `R`-linear in the multiplier. -/
theorem leftMulRegular_smul {n : ℤ} (r : R) (b : B.grading n) :
    leftMulRegular (r • b) = r • leftMulRegular b :=
  leftMulHomogeneous_smul (regularBimodule B) r b

/-- The unit of `B` acts as the identity. -/
theorem leftMulRegular_one (B : DifferentialGradedAlgebra.{u, u} R) :
    leftMulRegular (⟨1, SetLike.one_mem_graded B.grading⟩ : B.grading 0) =
      (dgCategory B).id (regularModule B) :=
  leftMulHomogeneous_one (regularBimodule B)

/-- A product of homogeneous elements acts as the composite of their actions. -/
theorem leftMulRegular_mul {n m : ℤ} (b : B.grading n) (c : B.grading m) :
    leftMulRegular
        (⟨(b : B.A) * (c : B.A), SetLike.mul_mem_graded b.property c.property⟩ :
          B.grading (n + m)) =
      (dgCategory B).comp (rfl : n + m = n + m) (leftMulRegular b) (leftMulRegular c) :=
  leftMulHomogeneous_mul (regularBimodule B) b c

/-- The differential of `B` acts by the differential of the differential graded category. -/
theorem leftMulRegular_d {n : ℤ} (b : B.grading n) :
    leftMulRegular (⟨B.d b, B.d_mem n b b.property⟩ : B.grading (n + 1)) =
      (dgCategory B).d (leftMulRegular b) :=
  leftMulHomogeneous_d (regularBimodule B) b

/-! ### The internal hom into the algebra -/

/-- The chosen presentation of the internal hom `S = Hom^•_B(T, B)` of a differential graded
`(A, B)`-bimodule `T`, as a right differential graded `A`-module. -/
abbrev homDualPresentation (T : Bimodule A B) :
    HomModuleData A B T.rightModule (regularModule B) T.leftAction :=
  homModulePresentation A B T.rightModule T.leftAction (regularModule B)

/-- The internal hom `S = Hom^•_B(T, B)` of a differential graded `(A, B)`-bimodule `T`, as a
right differential graded `A`-module. -/
def homDualModule (T : Bimodule A B) : DifferentialGradedModule.{u, u, u} A :=
  (homDualPresentation T).module

/-- The internal hom functor `Hom^•_B(T, -)` of Tag 0FQQ on a homogeneous endomorphism of the
regular module, with the resulting endomorphism of `S = Hom^•_B(T, B)` named at its own type. -/
def homDualMap (T : Bimodule A B) {n : ℤ}
    (f : (dgCategory B).Hom (regularModule B) (regularModule B) n) :
    HomogeneousMap A (homDualModule T) (homDualModule T) n :=
  (homDGFunctorData A B T.rightModule T.leftAction).functor.map f

/-- `homDualMap T` is additive. -/
theorem homDualMap_add (T : Bimodule A B) {n : ℤ}
    (f g : (dgCategory B).Hom (regularModule B) (regularModule B) n) :
    homDualMap T (f + g) = homDualMap T f + homDualMap T g :=
  (homDGFunctorData A B T.rightModule T.leftAction).functor.map_add f g

/-- `homDualMap T` is `R`-linear. -/
theorem homDualMap_smul (T : Bimodule A B) {n : ℤ} (r : R)
    (f : (dgCategory B).Hom (regularModule B) (regularModule B) n) :
    homDualMap T (r • f) = r • homDualMap T f :=
  (homDGFunctorData A B T.rightModule T.leftAction).functor.map_smul r f

/-- `homDualMap T` sends the identity of `B` to the identity of `S = Hom^•_B(T, B)`. -/
theorem homDualMap_id (T : Bimodule A B) :
    homDualMap T ((dgCategory B).id (regularModule B)) =
      (dgCategory A).id (homDualModule T) :=
  (homDGFunctorData A B T.rightModule T.leftAction).functor.map_id (regularModule B)

/-- `homDualMap T` preserves composition. -/
theorem homDualMap_comp (T : Bimodule A B) {m n k : ℤ} (h : m + n = k)
    (g : (dgCategory B).Hom (regularModule B) (regularModule B) m)
    (f : (dgCategory B).Hom (regularModule B) (regularModule B) n) :
    homDualMap T ((dgCategory B).comp h g f) =
      (dgCategory A).comp h (homDualMap T g) (homDualMap T f) :=
  (homDGFunctorData A B T.rightModule T.leftAction).functor.map_comp h g f

/-- `homDualMap T` commutes with the differentials of the differential graded categories. -/
theorem homDualMap_d (T : Bimodule A B) {n : ℤ}
    (f : (dgCategory B).Hom (regularModule B) (regularModule B) n) :
    homDualMap T ((dgCategory B).d f) = (dgCategory A).d (homDualMap T f) :=
  (homDGFunctorData A B T.rightModule T.leftAction).functor.map_d f

/-- The action of a homogeneous element `b ∈ B^n` on `S = Hom^•_B(T, B)`, as a homogeneous
right-`A`-linear endomorphism of `S` of degree `n`: it is the image, under the internal hom
functor `Hom^•_B(T, -)` of Tag 0FQQ, of left multiplication by `b` on `B`. -/
def homDualActionHomogeneous (T : Bimodule A B) {n : ℤ} (b : B.grading n) :
    HomogeneousMap A (homDualModule T) (homDualModule T) n :=
  homDualMap T (leftMulRegular b)

/-- The action of a homogeneous element of `B` on `S = Hom^•_B(T, B)`, read as a cochain of the
complex underlying `S`. -/
def homDualAction (T : Bimodule A B) (n : ℤ) :
    B.grading n →ₗ[R] Cochain (homDualModule T).toCochainComplex
      (homDualModule T).toCochainComplex n where
  toFun b := homogeneousMapCochain A (homDualModule T) n (homDualActionHomogeneous T b)
  map_add' b c := by
    rw [homDualActionHomogeneous, homDualActionHomogeneous, homDualActionHomogeneous,
      leftMulRegular_add, homDualMap_add, homogeneousMapCochain_add]
  map_smul' r b := by
    rw [RingHom.id_apply, homDualActionHomogeneous, homDualActionHomogeneous,
      leftMulRegular_smul, homDualMap_smul, homogeneousMapCochain_smul]

/-- The cochain `homDualAction T n b` is the cochain of `homDualActionHomogeneous T b`. -/
theorem homDualAction_apply (T : Bimodule A B) (n : ℤ) (b : B.grading n) :
    homDualAction T n b =
      homogeneousMapCochain A (homDualModule T) n (homDualActionHomogeneous T b) := rfl

/-- The left differential graded `B`-action on the complex underlying `S = Hom^•_B(T, B)`: a
homogeneous element of `B` acts by postcomposition with left multiplication by it. -/
def homDualLeftAction (T : Bimodule A B) :
    B.LeftAction (homDualModule T).toCochainComplex where
  action := homDualAction T
  map_one := by
    rw [homDualAction_apply, homDualActionHomogeneous, leftMulRegular_one, homDualMap_id,
      homogeneousMapCochain_id]
  map_mul n m b c := by
    rw [homDualAction_apply, homDualAction_apply, homDualAction_apply, homDualActionHomogeneous,
      homDualActionHomogeneous, homDualActionHomogeneous, leftMulRegular_mul, homDualMap_comp,
      homogeneousMapCochain_comp]
  map_d n b := by
    rw [homDualAction_apply, homDualAction_apply, homDualActionHomogeneous,
      homDualActionHomogeneous, leftMulRegular_d, homDualMap_d,
      homogeneousMapCochain_differential]

/-- **Stacks 0BZ0**, first assertion. For a differential graded `(A, B)`-bimodule `T`, the
internal hom `S = Hom_{Mod^{dg}_{(B, d)}}(T, B)` is a differential graded `(B, A)`-bimodule: the
right `A`-action is precomposition with the left action of `A` on `T`, and the left `B`-action is
postcomposition with left multiplication on `B`. -/
@[stacks 0BZ0 "the (B, A)-bimodule structure on S = Hom(T, B)"]
def homDualBimodule (T : Bimodule A B) : Bimodule B A where
  rightModule := homDualModule T
  leftAction :=
    ⟨homDualLeftAction T, fun n b =>
      ⟨homDualActionHomogeneous T b, fun p x =>
        homogeneousMapCochain_v' A (homDualModule T) n _ p (p + n) rfl x⟩⟩

/-! ### The action is left multiplication -/

/-- The left differential graded `B`-action carried by the bimodule of Tag 0BZ0 is the one
constructed above. -/
theorem homDualBimodule_leftAction (T : Bimodule A B) :
    (homDualBimodule T).leftAction.1 = homDualLeftAction T := rfl

/-- The action of a homogeneous `b ∈ B^n` on a homogeneous element of `S = Hom^•_B(T, B)`, as an
element of the degree-shifted graded piece. -/
def homDualSmul (T : Bimodule A B) {n p : ℤ} (b : B.grading n)
    (f : (homDualModule T).grading p) : (homDualModule T).grading (p + n) :=
  ((homDualLeftAction T).action n b).v p (p + n) (by omega) f

/-- **The left `B`-action on `S = Hom^•_B(T, B)` is left multiplication.** The homogeneous
right-`B`-linear map `T → B` attached to the action of a homogeneous `b ∈ B^n` on a degree-`p`
element `f` of `S` is `t ↦ b * f t`. -/
theorem homDualBimodule_action_apply (T : Bimodule A B) (n p q : ℤ) (b : B.grading n)
    (f : (homDualModule T).grading p) (x : T.rightModule.grading q) :
    ((((homDualPresentation T).homogeneousEquiv (p + n)) (homDualSmul T b f)).1
          (x : T.rightModule.M) : B.A) =
      (b : B.A) * ((((homDualPresentation T).homogeneousEquiv p) f).1
        (x : T.rightModule.M) : B.A) := by
  set v : (homDualModule T).M :=
    (homDualActionHomogeneous T b).1 (f : (homDualModule T).M) with hv
  set g : HomogeneousMap B T.rightModule (regularModule B) (n + p) :=
    homogeneousMapComp B (rfl : n + p = n + p) (leftMulRegular b)
      ((homDualPresentation T).homogeneousEquiv p f) with hg
  have hplus : v ∈ (homDualModule T).grading (p + n) :=
    (homDualActionHomogeneous T b).property.1 p (f : (homDualModule T).M) f.property
  have hcomm : v ∈ (homDualModule T).grading (n + p) := by
    rw [add_comm n p]; exact hplus
  have hval : homDualSmul T b f = ⟨v, hplus⟩ :=
    Subtype.ext (homogeneousMapCochain_v' A (homDualModule T) n
      (homDualActionHomogeneous T b) p (p + n) rfl f)
  rw [hval]
  refine (homogeneousEquiv_val_apply_congr (homDualPresentation T)
    (show p + n = n + p by omega) ⟨v, hplus⟩
    (⟨v, hcomm⟩ : (homDualModule T).grading (n + p)) rfl x).trans ?_
  have hpost : v = (((homDualPresentation T).homogeneousEquiv (n + p)).symm g).1 :=
    homPostcompHomogeneousMap_apply A B T.rightModule T.leftAction
      (homDualPresentation T) (homDualPresentation T) n p (leftMulRegular b) f
  rw [show (⟨v, hcomm⟩ : (homDualModule T).grading (n + p)) =
      ((homDualPresentation T).homogeneousEquiv (n + p)).symm g from Subtype.ext hpost,
    LinearEquiv.apply_symm_apply]
  exact leftMulRegular_apply b _

end DifferentialGraded.Bimodule

end
