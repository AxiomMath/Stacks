module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorCoproduct
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorBimoduleVariable
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorEquivalence

/-! # Tensoring with a module commutes with direct sums in the bimodule variable

Let `B` and `C` be differential graded algebras over a commutative ring `R` and let `W` be a
right differential graded `B`-module. A differential graded `(B, C)`-bimodule is the same thing
as a right differential graded module over `Bᵒᵖ ⊗_R C` (Tag 0FQJ), and the ordinary tensor
functor `W ⊗_B - : Mod_{(Bᵒᵖ ⊗_R C, d)} ⥤ Mod_{(C, d)}` of Tag 09LM carries the direct sum
`⨁ᵢ Yᵢ` of a family of such modules to the direct sum `⨁ᵢ (W ⊗_B Yᵢ)`.

## Main definitions

* `DifferentialGraded.Bimodule.bimoduleDirectSumBalancedLinear` and
  `DifferentialGraded.Bimodule.bimoduleDirectSumBalanced`: the balanced bilinear map out of `W`
  and `⨁ᵢ Yᵢ` assembled from a family of homomorphisms out of the `W ⊗_B Yᵢ`.
* `DifferentialGraded.Bimodule.bimoduleTensorDirectSumDesc`: the resulting descent
  `W ⊗_B (⨁ᵢ Yᵢ) ⟶ T`.

## Main results

* `DifferentialGraded.Bimodule.isColimit_tensorBimoduleFunctor_directSumCofan`: the images of the
  coprojections `Yᵢ ⟶ ⨁ⱼ Yⱼ` exhibit `W ⊗_B (⨁ᵢ Yᵢ)` as the direct sum of the `W ⊗_B Yᵢ`.
* `DifferentialGraded.Bimodule.preservesColimit_tensorBimoduleFunctor`: the same statement in the
  form `CategoryTheory.Limits.PreservesColimit`, which is how the dévissage consumes it.

## Implementation notes

*This is the mirror image of
`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensorCoproduct.lean`*, where the direct
sum is taken in the module variable instead. The architecture is the same: the only handles on
`W ⊗_B N` are the universal balanced bilinear map
`DifferentialGraded.Bimodule.tensorPure`, the extensionality principle
`DifferentialGraded.Bimodule.tensorObj_hom_ext` and the formula
`DifferentialGraded.Bimodule.tensorBimoduleFunctor_map_pure` for the functor on pure tensors, so
a cocone is descended by lifting a balanced bilinear map assembled from its legs by the universal
property of the direct sum of `R`-modules, and both halves of the universal property are checked
on pure tensors.

*What the direct sum being the second factor changes.* The assembled bilinear map is a
`DirectSum.toModule` sandwiched between two flips, and the only genuinely new ingredient is the
balancing condition: it moves a right scalar of `B` from `W` across the pure tensors into the
*left* action of `B` on the direct sum, so that condition needs the left action on `⨁ᵢ Yᵢ` to be
componentwise. That is `DifferentialGraded.Bimodule.bimoduleDirectSumLeftActionTotal_lof`, read
off from `DifferentialGraded.Bimodule.leftAction_val` — which rewrites the cochain component in
which the condition is phrased as the totalized action — together with
`DifferentialGraded.Bimodule.ofTensorModule_leftActionTotal_apply`, which evaluates that
totalized action as the action of a single element of `Bᵒᵖ ⊗_R C` with a Koszul sign depending
only on the two degrees. The sign is the same on a coprojection as on the element it is the
coprojection of, so all that remains is that the right action is componentwise.

*Where the honest type is used.* The carrier of `DifferentialGradedModule.directSumObj` is the
bare direct sum `⨁ᵢ (Yᵢ).M` only up to unfolding at default transparency, and the bimodule
attached to a module over `Bᵒᵖ ⊗_R C` has that same carrier again only up to unfolding. So,
exactly as in `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedCategoryCoproducts.lean`,
every elementwise fact is phrased at the bare direct sum and the structure fields of the balanced
bilinear map are discharged by `exact`.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the tensor functor.
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ), bimodules as modules
  over the graded tensor product.
* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI), direct sums of
  differential graded modules.
* [Stacks Project, Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5), where the dévissage
  this serves is carried out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (B C : DifferentialGradedAlgebra.{u, u} R)

/-- The element of `Bᵒᵖ ⊗_R C` through which a homogeneous `b : B^n` acts on the left of the
bimodule attached to a right differential graded `Bᵒᵖ ⊗_R C`-module: the image of `b` under the
left inclusion, read in the graded opposite. -/
def bimoduleDirectSumIncludeLeft {n : ℤ} (b : B.grading n) : (tensorAlgebra B C).A :=
  GradedTensorProduct.includeLeft (oppAlgebra B).grading C.grading
    ((DifferentialGradedAlgebra.opposite R B).equiv.symm (b : B.A))

section Decidable

variable (W : DifferentialGradedModule.{u, u, u} B) {ι : Type u} [DecidableEq ι]
  (Y : ι → DifferentialGradedModule.{u, u, u} (tensorAlgebra B C))

/-- **The left action of `B` on a direct sum of right differential graded `Bᵒᵖ ⊗_R C`-modules is
componentwise.** Both sides are the action of a single element of `Bᵒᵖ ⊗_R C` with the same
Koszul sign, since a coprojection of a homogeneous element has the degree of that element. -/
theorem bimoduleDirectSumLeftActionTotal_lof (n q : ℤ) (b : B.grading n) (j : ι)
    {z : (Y j).M} (hz : z ∈ (Y j).grading q) :
    leftActionTotal B C (ofTensorModule B C (directSumObj Y)).rightModule
        (ofTensorModule B C (directSumObj Y)).leftAction.1 (b : B.A)
        (DirectSum.lof R ι (fun i => (Y i).M) j z) =
      DirectSum.lof R ι (fun i => (Y i).M) j
        (leftActionTotal B C (ofTensorModule B C (Y j)).rightModule
          (ofTensorModule B C (Y j)).leftAction.1 (b : B.A) z) :=
  calc _ = ((n * q).negOnePow : ℤ) • (MulOpposite.op (bimoduleDirectSumIncludeLeft B C b) •
          DirectSum.lof R ι (fun i => (Y i).M) j z) :=
        ofTensorModule_leftActionTotal_apply B C (directSumObj Y) b
          ⟨DirectSum.lof R ι (fun i => (Y i).M) j z, lof_mem_directSumGrading Y j hz⟩
    _ = ((n * q).negOnePow : ℤ) • DirectSum.lof R ι (fun i => (Y i).M) j
          (MulOpposite.op (bimoduleDirectSumIncludeLeft B C b) • z) := by
        rw [op_smul_lof]
    _ = DirectSum.lof R ι (fun i => (Y i).M) j (((n * q).negOnePow : ℤ) •
          (MulOpposite.op (bimoduleDirectSumIncludeLeft B C b) • z)) :=
        (map_zsmul (DirectSum.lof R ι (fun i => (Y i).M) j) _ _).symm
    _ = _ := congrArg (DirectSum.lof R ι (fun i => (Y i).M) j)
        (ofTensorModule_leftActionTotal_apply B C (Y j) b ⟨z, hz⟩).symm

/-- **The right action of `C` on a direct sum of right differential graded `Bᵒᵖ ⊗_R C`-modules is
componentwise**, for the action read through the right inclusion of `C`. The element of the
direct sum is taken as a parameter `y` together with an equation for it, so that both actions are
the ones attached to the bimodules rather than to the modules over `Bᵒᵖ ⊗_R C`. -/
theorem bimoduleDirectSum_op_smul_of (j : ι) (c : C.A)
    (z : (ofTensorModule B C (Y j)).rightModule.M)
    (y : (ofTensorModule B C (directSumObj Y)).rightModule.M)
    (hy : y = DirectSum.of (fun i => (Y i).M) j z) :
    MulOpposite.op c • y = DirectSum.of (fun i => (Y i).M) j (MulOpposite.op c • z) := by
  subst hy
  exact op_smul_of Y j z (GradedTensorProduct.includeRight (oppAlgebra B).grading C.grading c)

/-- **The differential of a direct sum of right differential graded `Bᵒᵖ ⊗_R C`-modules is
componentwise**, stated for the differential of the attached bimodules. -/
theorem bimoduleDirectSum_d_of (j : ι) (z : (Y j).M) :
    (ofTensorModule B C (directSumObj Y)).rightModule.d
        (DirectSum.of (fun i => (Y i).M) j z) =
      DirectSum.of (fun i => (Y i).M) j ((ofTensorModule B C (Y j)).rightModule.d z) :=
  directSumD_of Y j z

variable {T : DifferentialGradedModule.{u, u, u} C}
  (g : ∀ i, tensorObj (ofTensorModule B C (Y i)) W ⟶ T)

/-- The bilinear map underlying `DifferentialGraded.Bimodule.bimoduleDirectSumBalanced`, with the
direct sum at its bare type in the second variable: on the `i`-th summand it is the universal
pure tensor of `Yᵢ` followed by `gᵢ`. -/
def bimoduleDirectSumBalancedLinear : W.M →ₗ[R] (⨁ i, (Y i).M) →ₗ[R] T.M :=
  LinearMap.flip (DirectSum.toModule R ι (W.M →ₗ[R] T.M)
    (fun i => (LinearMap.flip
      ((tensorPure (ofTensorModule B C (Y i)) W).toLinearMap.compr₂ (g i).toFun) :
        (Y i).M →ₗ[R] W.M →ₗ[R] T.M)))

/-- The bilinear map of `DifferentialGraded.Bimodule.bimoduleDirectSumBalancedLinear` on the
`j`-th coprojection. -/
theorem bimoduleDirectSumBalancedLinear_lof (x : W.M) (j : ι) (z : (Y j).M) :
    bimoduleDirectSumBalancedLinear B C W Y g x (DirectSum.lof R ι (fun i => (Y i).M) j z) =
      (g j).toFun ((tensorPure (ofTensorModule B C (Y j)) W).toLinearMap x z) :=
  congrArg (fun f : W.M →ₗ[R] T.M => f x)
    (DirectSum.toModule_lof (R := R)
      (φ := fun i => (LinearMap.flip
        ((tensorPure (ofTensorModule B C (Y i)) W).toLinearMap.compr₂ (g i).toFun) :
          (Y i).M →ₗ[R] W.M →ₗ[R] T.M)) j z)

/-- `DifferentialGraded.Bimodule.bimoduleDirectSumBalancedLinear_lof`, stated for
`DirectSum.of` rather than for `DirectSum.lof`. -/
theorem bimoduleDirectSumBalancedLinear_of (x : W.M) (j : ι) (z : (Y j).M) :
    bimoduleDirectSumBalancedLinear B C W Y g x (DirectSum.of (fun i => (Y i).M) j z) =
      (g j).toFun ((tensorPure (ofTensorModule B C (Y j)) W).toLinearMap x z) := by
  rw [← DirectSum.lof_eq_of (R := R)]
  exact bimoduleDirectSumBalancedLinear_lof B C W Y g x j z

/-- **The assembled bilinear map adds degrees.** -/
theorem bimoduleDirectSumBalancedLinear_mem_grading (p q : ℤ) (x : W.grading p)
    {y : ⨁ i, (Y i).M} (hy : y ∈ (directSumObj Y).grading q) :
    bimoduleDirectSumBalancedLinear B C W Y g x y ∈ T.grading (p + q) := by
  refine directSumObj_grading_induction Y q
    (fun y => bimoduleDirectSumBalancedLinear B C W Y g x y ∈ T.grading (p + q)) ?_ ?_ ?_ y hy
  · simpa only [map_zero] using (T.grading (p + q)).zero_mem
  · intro j z hz
    rw [bimoduleDirectSumBalancedLinear_lof]
    exact (g j).map_grading _ _
      ((tensorPure (ofTensorModule B C (Y j)) W).map_grading p q x ⟨z, hz⟩)
  · intro y₁ y₂ h₁ h₂
    simpa only [map_add] using (T.grading (p + q)).add_mem h₁ h₂

/-- **The assembled bilinear map satisfies the graded Leibniz rule.** -/
theorem bimoduleDirectSumBalancedLinear_d (p : ℤ) (x : W.grading p)
    (y : (ofTensorModule B C (directSumObj Y)).rightModule.M) :
    T.d (bimoduleDirectSumBalancedLinear B C W Y g x y) =
      bimoduleDirectSumBalancedLinear B C W Y g (W.d x) y + (p.negOnePow : ℤ) •
        bimoduleDirectSumBalancedLinear B C W Y g x
          ((ofTensorModule B C (directSumObj Y)).rightModule.d y) := by
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero, add_zero]
  | of j z =>
    have hg (w : (tensorObj (ofTensorModule B C (Y j)) W).M) :
        (g j).toFun ((tensorObj (ofTensorModule B C (Y j)) W).d w) = T.d ((g j).toFun w) :=
      LinearMap.congr_fun (g j).map_d w
    rw [bimoduleDirectSum_d_of, bimoduleDirectSumBalancedLinear_of,
      bimoduleDirectSumBalancedLinear_of, bimoduleDirectSumBalancedLinear_of, ← hg,
      (tensorPure (ofTensorModule B C (Y j)) W).map_d p x z, map_add, map_zsmul]
  | add y₁ y₂ h₁ h₂ =>
    simp only [map_add, smul_add, h₁, h₂]
    abel

/-- **The assembled bilinear map is balanced over `B`.** The second argument of the right-hand
side is taken as a parameter `w` together with an equation for it, so that the statement can be
applied against the `balance` field without reproducing the degree bookkeeping of its right-hand
side. -/
theorem bimoduleDirectSumBalancedLinear_balance (p q n : ℤ) (x : W.grading p) (b : B.grading n)
    {y : ⨁ i, (Y i).M} (hy : y ∈ (directSumObj Y).grading q)
    {w : (ofTensorModule B C (directSumObj Y)).rightModule.M}
    (hw : w = leftActionTotal B C (ofTensorModule B C (directSumObj Y)).rightModule
      (ofTensorModule B C (directSumObj Y)).leftAction.1 (b : B.A) y) :
    bimoduleDirectSumBalancedLinear B C W Y g (MulOpposite.op (b : B.A) • (x : W.M)) y =
      bimoduleDirectSumBalancedLinear B C W Y g x w := by
  subst hw
  refine directSumObj_grading_induction Y q
    (fun y => bimoduleDirectSumBalancedLinear B C W Y g
        (MulOpposite.op (b : B.A) • (x : W.M)) y =
      bimoduleDirectSumBalancedLinear B C W Y g x
        (leftActionTotal B C (ofTensorModule B C (directSumObj Y)).rightModule
          (ofTensorModule B C (directSumObj Y)).leftAction.1 (b : B.A) y)) ?_ ?_ ?_ y hy
  · simp only [map_zero]
  · intro j z hz
    have hb := (tensorPure (ofTensorModule B C (Y j)) W).balance p q n x ⟨z, hz⟩ b
    rw [leftAction_val B C (ofTensorModule B C (Y j)) n q b ⟨z, hz⟩] at hb
    rw [bimoduleDirectSumBalancedLinear_lof,
      bimoduleDirectSumLeftActionTotal_lof B C Y n q b j hz,
      bimoduleDirectSumBalancedLinear_lof]
    exact congrArg (g j).toFun hb
  · intro y₁ y₂ h₁ h₂
    simp only [map_add, h₁, h₂]

/-- **The assembled bilinear map is right `C`-linear in the second variable.** -/
theorem bimoduleDirectSumBalancedLinear_smul_right (x : W.M)
    (y : (ofTensorModule B C (directSumObj Y)).rightModule.M) (c : C.A) :
    bimoduleDirectSumBalancedLinear B C W Y g x (MulOpposite.op c • y) =
      MulOpposite.op c • bimoduleDirectSumBalancedLinear B C W Y g x y := by
  induction y using DirectSum.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | of j z =>
    rw [bimoduleDirectSum_op_smul_of B C Y j c z _ rfl, bimoduleDirectSumBalancedLinear_of,
      bimoduleDirectSumBalancedLinear_of, (tensorPure (ofTensorModule B C (Y j)) W).map_right,
      (g j).map_smul]
  | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]

/-- **The balanced bilinear map assembled from a family of maps out of the summands.** Given
homomorphisms `gᵢ : W ⊗_B Yᵢ ⟶ T`, the map `(x, y) ↦ gᵢ (x ⊗ yᵢ)` summed over the components of
`y` is a balanced bilinear map from `W` and `⨁ᵢ Yᵢ` to `T`. -/
def bimoduleDirectSumBalanced :
    BalancedBilinearMap W (ofTensorModule B C (directSumObj Y)) T where
  toLinearMap := bimoduleDirectSumBalancedLinear B C W Y g
  map_grading p q x y := bimoduleDirectSumBalancedLinear_mem_grading B C W Y g p q x y.property
  map_d p x y := bimoduleDirectSumBalancedLinear_d B C W Y g p x y
  balance p q n x y b :=
    bimoduleDirectSumBalancedLinear_balance B C W Y g p q n x b y.property
      (leftAction_val B C (ofTensorModule B C (directSumObj Y)) n q b y)
  map_right x y c := bimoduleDirectSumBalancedLinear_smul_right B C W Y g x y c

/-- The descent `W ⊗_B (⨁ᵢ Yᵢ) ⟶ T` of a family of homomorphisms `W ⊗_B Yᵢ ⟶ T`: the lift of
`DifferentialGraded.Bimodule.bimoduleDirectSumBalanced` along the universal property of
Tag 09LM. -/
def bimoduleTensorDirectSumDesc : tensorObj (ofTensorModule B C (directSumObj Y)) W ⟶ T :=
  ((tensorDGFunctor (ofTensorModule B C (directSumObj Y))).universal W T
    (bimoduleDirectSumBalanced B C W Y g)).choose

/-- The descent of `DifferentialGraded.Bimodule.bimoduleTensorDirectSumDesc` on a pure
tensor. -/
theorem bimoduleTensorDirectSumDesc_pure (x : W.M)
    (y : (ofTensorModule B C (directSumObj Y)).rightModule.M) :
    (bimoduleTensorDirectSumDesc B C W Y g).toFun
        ((tensorPure (ofTensorModule B C (directSumObj Y)) W).toLinearMap x y) =
      bimoduleDirectSumBalancedLinear B C W Y g x y :=
  ((tensorDGFunctor (ofTensorModule B C (directSumObj Y))).universal W T
    (bimoduleDirectSumBalanced B C W Y g)).choose_spec.1 x y

/-- **The ordinary tensor product commutes with direct sums in the bimodule variable.** The
images under `W ⊗_B -` of the coprojections `Yᵢ ⟶ ⨁ⱼ Yⱼ` exhibit `W ⊗_B (⨁ᵢ Yᵢ)` as the direct
sum of the family `W ⊗_B Yᵢ`.

A cocone is descended by lifting the balanced bilinear map assembled from its legs, and both
halves of the universal property are checked on pure tensors by
`DifferentialGraded.Bimodule.tensorObj_hom_ext`. -/
def isColimit_tensorBimoduleFunctor_directSumCofan :
    IsColimit (Cofan.mk (f := fun i => (tensorBimoduleFunctor B C W).obj (Y i))
      ((tensorBimoduleFunctor B C W).obj (directSumObj Y))
      (fun i => (tensorBimoduleFunctor B C W).map (directSumInj Y i))) := by
  classical
  change IsColimit (Cofan.mk (f := fun i => tensorObj (ofTensorModule B C (Y i)) W)
    (tensorObj (ofTensorModule B C (directSumObj Y)) W)
    (fun i => (tensorBimoduleFunctor B C W).map (directSumInj Y i)))
  refine Cofan.IsColimit.mk _
    (fun s => bimoduleTensorDirectSumDesc B C W Y (fun i => s.inj i)) (fun s j => ?_)
    (fun s m hm => ?_)
  · refine tensorObj_hom_ext (ofTensorModule B C (Y j)) W _ _ fun x y => ?_
    change (bimoduleTensorDirectSumDesc B C W Y (fun i => s.inj i)).toFun
        (((tensorBimoduleFunctor B C W).map (directSumInj Y j)).toFun
          ((tensorPure (ofTensorModule B C (Y j)) W).toLinearMap x y)) =
      (s.inj j).toFun ((tensorPure (ofTensorModule B C (Y j)) W).toLinearMap x y)
    rw [tensorBimoduleFunctor_map_pure]
    exact (bimoduleTensorDirectSumDesc_pure B C W Y (fun i => s.inj i) x _).trans
      (bimoduleDirectSumBalancedLinear_lof B C W Y (fun i => s.inj i) x j y)
  · refine tensorObj_hom_ext (ofTensorModule B C (directSumObj Y)) W _ _ fun x y => ?_
    change m.toFun ((tensorPure (ofTensorModule B C (directSumObj Y)) W).toLinearMap x y) =
      (bimoduleTensorDirectSumDesc B C W Y (fun i => s.inj i)).toFun
        ((tensorPure (ofTensorModule B C (directSumObj Y)) W).toLinearMap x y)
    rw [bimoduleTensorDirectSumDesc_pure B C W Y (fun i => s.inj i)]
    induction y using DirectSum.induction_on with
    | zero =>
      have h0 : (tensorPure (ofTensorModule B C (directSumObj Y)) W).toLinearMap x 0 = 0 :=
        map_zero _
      rw [h0]
      simp only [map_zero]
    | of j z =>
      have h := congrArg (fun f : tensorObj (ofTensorModule B C (Y j)) W ⟶ s.pt =>
        f.toFun ((tensorPure (ofTensorModule B C (Y j)) W).toLinearMap x z)) (hm j)
      change m.toFun (((tensorBimoduleFunctor B C W).map (directSumInj Y j)).toFun _) = _ at h
      rw [tensorBimoduleFunctor_map_pure] at h
      rw [bimoduleDirectSumBalancedLinear_of]
      exact h
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add ((tensorPure (ofTensorModule B C (directSumObj Y)) W).toLinearMap x) y₁ y₂,
        map_add m.toFun, h₁, h₂,
        map_add (bimoduleDirectSumBalancedLinear B C W Y (fun i => s.inj i) x) y₁ y₂]

end Decidable

/-- **Tensoring with `W` preserves the direct sum of a family of right differential graded
`Bᵒᵖ ⊗_R C`-modules**, in the form `CategoryTheory.Limits.PreservesColimit` at the chosen direct
sum `DifferentialGradedModule.directSumObj`. -/
theorem preservesColimit_tensorBimoduleFunctor
    (W : DifferentialGradedModule.{u, u, u} B) {ι : Type u}
    (Y : ι → DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) :
    PreservesColimit (Discrete.functor Y) (tensorBimoduleFunctor B C W) := by
  classical
  exact preservesColimit_of_preserves_colimit_cocone (isColimit_directSumObj Y)
    ((Cofan.isColimitMapCoconeEquiv (tensorBimoduleFunctor B C W) Y
      (Cofan.mk (directSumObj Y) (directSumInj Y))).symm
        (isColimit_tensorBimoduleFunctor_directSumCofan B C W Y))

end DifferentialGraded.Bimodule

end
