module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorBimodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomFunctorAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInternalHomModule

/-!
# Associativity of the tensor product of differential graded modules and bimodules

Let `𝒜`, `𝒜'` and `ℬ` be sheaves of differential graded algebras on a site, let `𝒫` be a right
differential graded `𝒜`-module, `𝒩` a differential graded `(𝒜, 𝒜')`-bimodule and `ℒ` a
differential graded `(𝒜', ℬ)`-bimodule. Then

`(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ = 𝒫 ⊗_𝒜 (𝒩 ⊗_{𝒜'} ℒ)`

as right differential graded `ℬ`-modules, where `𝒩 ⊗_{𝒜'} ℒ` is the differential graded
`(𝒜, ℬ)`-bimodule `SheafOfModules.RelativeTensor.bimoduleTensor`.

## Main definitions

* `SheafOfModules.IsTensorProductCore.compBalanced`: composing a local homomorphism out of a
  tensor product with its multiplication map gives a balanced bilinear family.
* `SheafOfModules.IsTensorProduct.leftTmulHom`: for a local section `x` of `𝒫`, the local
  homomorphism `n ↦ x ⊗ n` of right differential graded `𝒜'`-modules `𝒩 → 𝒫 ⊗_𝒜 𝒩`.
* `SheafOfModules.IsTensorProduct.assocTmul`: the multiplication `x ⊗ t` of `𝒫` with
  `𝒩 ⊗_{𝒜'} ℒ` with values in `(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ`: it is `(n ↦ x ⊗ n) ⊗ 1` applied to `t`.

## Main results

* `SheafOfModules.IsTensorProduct.assoc`: **`(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ` is the tensor product of `𝒫`
  and `𝒩 ⊗_{𝒜'} ℒ`**, with multiplication map `assocTmul`, so that
  `SheafOfModules.IsTensorProduct.uniqueIso` identifies it with `𝒫 ⊗_𝒜 (𝒩 ⊗_{𝒜'} ℒ)` by
  `(x ⊗ n) ⊗ y ↦ x ⊗ (n ⊗ y)`.

## Implementation notes

The multiplication `x ⊗ t` cannot be written on a local section `t` of `𝒩 ⊗_{𝒜'} ℒ`, which is
not a sum of pure tensors; it is the value at `t` of the local homomorphism `ρ_x ⊗ 1`, where
`ρ_x : 𝒩 → 𝒫 ⊗_𝒜 𝒩` is `n ↦ x ⊗ n`, and its laws are those of `ρ_x` transported by
`SheafOfModules.IsTensorProduct.transport`.

The universal property is checked through the internal hom `SheafHom^dg_ℬ(ℒ, -)`, a right
differential graded `𝒜'`-module: a local homomorphism out of `(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ` is a local
homomorphism `𝒫 ⊗_𝒜 𝒩 → SheafHom^dg_ℬ(ℒ, -)` (`SheafOfModules.balancedEquivDg`), which is a
balanced family on `𝒫 × 𝒩`, and such a family is the same as a balanced family on
`𝒫 × (𝒩 ⊗_{𝒜'} ℒ)` because a local homomorphism out of `𝒩 ⊗_{𝒜'} ℒ` is determined by its values
on pure tensors.

## References

* [Stacks Project, Tag 0FTL](https://stacks.math.columbia.edu/tag/0FTL)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe t a s v u

namespace SheafOfModules

section Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Composing a local homomorphism with a multiplication map -/

section Core

variable {A B : DifferentialGradedAlgebra.{t, a} R} {M : DifferentialGradedModule.{t, a, s} A}
  {N : DifferentialGradedBimodule.{t, a, s} A B} {T L : DifferentialGradedModule.{t, a, s} B}

namespace IsTensorProductCore

/-- The balanced bilinear family `(x, y) ↦ f (x ⊗ y)` attached to a local homomorphism `f` out of
a module carrying the multiplication map and the laws of a tensor product. -/
def compBalanced (hc : IsTensorProductCore M N T) {n : ℤ} {U : C} (f : LocalHom T L n U) :
    LocalBalancedBilinear M N L n U where
  app i j k hijk V := (f.app (i + j) k hijk V).compHom.comp (hc.tmul i j (op V.left))
  map_smul_left i j k hijk V r x y := by
    change f.app (i + j) k hijk V (hc.tmul i j (op V.left) (r • x) y) =
      r • f.app (i + j) k hijk V (hc.tmul i j (op V.left) x y)
    rw [hc.tmul_smul_left, f.map_smul]
  map_smul_right i j k hijk V r x y := by
    change f.app (i + j) k hijk V (hc.tmul i j (op V.left) x (r • y)) =
      r • f.app (i + j) k hijk V (hc.tmul i j (op V.left) x y)
    rw [hc.tmul_smul_right, f.map_smul]
  naturality i j k hijk {V W} q x y := by
    change (L.complex.X k).val.map q.left.op
        (f.app (i + j) k hijk V (hc.tmul i j (op V.left) x y)) =
      f.app (i + j) k hijk W (hc.tmul i j (op W.left) ((M.complex.X i).val.map q.left.op x)
        ((N.complex.X j).val.map q.left.op y))
    rw [f.naturality, hc.tmul_naturality]
  balanced i p j k hijk V x b y := by
    change f.app (i + p + j) k hijk V
        (hc.tmul (i + p) j (op V.left) ((M.mul i p).app (op V.left) x b) y) =
      f.app (i + (p + j)) k (by omega) V
        (hc.tmul i (p + j) (op V.left) x ((N.leftMul p j).app (op V.left) b y))
    exact LocalGradedHom.app_heq_congr f.toLocalGradedHom (by omega) _ _ V
      (hc.tmul_balanced i p j (op V.left) x b y)
  map_rightMul i j p k hijk V x y b := by
    change f.app (i + (j + p)) (k + p) (by omega) V
        (hc.tmul i (j + p) (op V.left) x ((N.rightMul j p).app (op V.left) y b)) =
      (L.mul k p).app (op V.left) (f.app (i + j) k hijk V (hc.tmul i j (op V.left) x y)) b
    rw [← f.isLinear (i + j) k hijk p V]
    exact LocalGradedHom.app_heq_congr f.toLocalGradedHom (by omega) _ _ V
      (hc.tmul_rightMul i j p (op V.left) x y b).symm

/-- The value of `compBalanced f` at `(x, y)` is `f (x ⊗ y)`. -/
@[simp]
theorem compBalanced_app (hc : IsTensorProductCore M N T) {n : ℤ} {U : C}
    (f : LocalHom T L n U) (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
    (x : (M.complex.X i).val.obj (op V.left)) (y : (N.complex.X j).val.obj (op V.left)) :
    (hc.compBalanced f).app i j k hijk V x y = f.app (i + j) k hijk V (hc.tmul i j _ x y) :=
  rfl

end IsTensorProductCore

end Core

/-! ### The local homomorphism `n ↦ x ⊗ n` -/

section LeftTmul

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
  {A A' : DifferentialGradedAlgebra.{t, a} R} {P : DifferentialGradedModule.{t, a, s} A}
  {N : DifferentialGradedBimodule.{t, a, s} A A'} {Y : DifferentialGradedModule.{t, a, s} A'}

namespace IsTensorProduct

/-- For a local section `x` of `𝒫` of degree `i` over `U`, the degree-`i` local homomorphism
`n ↦ x ⊗ n` of right differential graded `𝒜'`-modules `𝒩|_U → (𝒫 ⊗_𝒜 𝒩)|_U`. -/
noncomputable def leftTmulHom (hY : IsTensorProduct P N Y) {i : ℤ} {U : C}
    (x : (P.complex.X i).val.obj (op U)) : LocalHom N.toRightModule Y i U :=
  balancedHomDg (hY.tmulBalanced U) (add_zero i) (Over.mk (𝟙 U)) x

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The value of `n ↦ x ⊗ n` at a local section `n` of `𝒩` over `W` is the tensor product of
the restriction of `x` to `W` with `n`. -/
theorem leftTmulHom_app (hY : IsTensorProduct P N Y) {i : ℤ} {U : C}
    (x : (P.complex.X i).val.obj (op U)) (j k : ℤ) (hjk : j + i = k) (W : Over U)
    (n : (N.complex.X j).val.obj (op W.left)) :
    (hY.leftTmulHom x).app j k hjk W n =
      castHom Y.complex.X (by omega) (op W.left)
        (hY.tmul i j (op W.left) (restrictAlong (P.complex.X i) W.hom x) n) := by
  rw [leftTmulHom, balancedHomDg_eq]
  exact hY.tmulBalanced_app U i j k (by omega) _ _ n

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The local homomorphism `n ↦ x ⊗ n` is additive in `x`. -/
theorem leftTmulHom_add (hY : IsTensorProduct P N Y) {i : ℤ} {U : C}
    (x x' : (P.complex.X i).val.obj (op U)) :
    hY.leftTmulHom (x + x') = hY.leftTmulHom x + hY.leftTmulHom x' :=
  LocalHom.ext fun j k hjk W n => by
    rw [LocalHom.add_app, leftTmulHom_app, leftTmulHom_app, leftTmulHom_app]
    rw [restrictAlong_add]
    exact (congrArg (castHom Y.complex.X _ (op W.left))
      (hY.tmul_add_left i j (op W.left) _ _ n)).trans (map_add _ _ _)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The local homomorphism `n ↦ x ⊗ n` is compatible with restriction along a morphism of the
site. -/
theorem leftTmulHom_restrict (hY : IsTensorProduct P N Y) {i : ℤ} {U U' : C} (q : U' ⟶ U)
    (x : (P.complex.X i).val.obj (op U)) :
    (hY.leftTmulHom x).restrict q = hY.leftTmulHom (restrictAlong (P.complex.X i) q x) :=
  LocalHom.ext fun j k hjk W n => by
    change (hY.leftTmulHom x).app j k hjk (Over.mk (W.hom ≫ q)) n = _
    rw [leftTmulHom_app, leftTmulHom_app]
    congr 3
    exact (P.complex.X i).val.map_comp_apply q.op W.hom.op x

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The multiplication map of a tensor product respects heterogeneous equalities in both
variables. -/
theorem tmul_heq {M : DifferentialGradedModule.{t, a, s} A}
    {T : DifferentialGradedModule.{t, a, s} A'}
    (hT : IsTensorProduct M N T) {i i' j j' : ℤ} (hi : i = i') (hj : j = j') (U : Cᵒᵖ)
    {x : (M.complex.X i).val.obj U} {x' : (M.complex.X i').val.obj U} (hx : HEq x x')
    {y : (N.complex.X j).val.obj U} {y' : (N.complex.X j').val.obj U} (hy : HEq y y') :
    HEq (hT.tmul i j U x y) (hT.tmul i' j' U x' y') := by
  subst hi hj
  rw [eq_of_heq hx, eq_of_heq hy]

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- **The differential of `n ↦ x ⊗ n` is `n ↦ d x ⊗ n`**, by the Leibniz rule of the
multiplication map. -/
theorem leftTmulHom_diffAt (hY : IsTensorProduct P N Y) {i : ℤ} {U : C}
    (x : (P.complex.X i).val.obj (op U)) :
    (hY.leftTmulHom x).diffAt =
      hY.leftTmulHom ((P.complex.d i (i + 1)).val.app (op U) x) :=
  LocalHom.ext fun j k hjk W n => by
    rw [LocalHom.diffAt_app, leftTmulHom_app, leftTmulHom_app, leftTmulHom_app,
      d_castHom_app Y.complex (show i + j = j + i by omega) (show i + j + 1 = k by omega)]
    rw [restrictAlong_homSections]
    generalize restrictAlong (P.complex.X i) W.hom x = x'
    rw [hY.tmul_d_castHom i j (op W.left) x' n, map_add, map_zsmul, castHom_castHom,
      castHom_castHom, add_sub_cancel_right]

end IsTensorProduct

end LeftTmul

/-! ### The multiplication `x ⊗ t` of `𝒫` with `𝒩 ⊗_{𝒜'} ℒ` -/

section Assoc

variable [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
  {A A' B : DifferentialGradedAlgebra.{t, a} R} {P : DifferentialGradedModule.{t, a, s} A}
  {N : DifferentialGradedBimodule.{t, a, s} A A'} {L : DifferentialGradedBimodule.{t, a, s} A' B}
  {Y : DifferentialGradedModule.{t, a, s} A'} {T W : DifferentialGradedModule.{t, a, s} B}
  (hY : IsTensorProduct P N Y) (hT : IsTensorProduct N.toRightModule L T)
  (hW : IsTensorProduct Y L W)

namespace IsTensorProduct

/-- The local homomorphism `t ↦ x ⊗ t` from `𝒩 ⊗_{𝒜'} ℒ` to `(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ` attached to a
local section `x` of `𝒫`: the tensor product with `ℒ` of `n ↦ x ⊗ n`. -/
noncomputable def assocHom {i : ℤ} {U : C} (x : (P.complex.X i).val.obj (op U)) :
    LocalHom T W i U :=
  hT.transport hW (hY.leftTmulHom x)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- **`x ⊗ (n ⊗ y) = (x ⊗ n) ⊗ y`.** -/
theorem assocHom_tmul {i : ℤ} {U : C} (x : (P.complex.X i).val.obj (op U)) (j j' kk : ℤ)
    (hk : j + j' + i = kk) (V : Over U) (n : (N.complex.X j).val.obj (op V.left))
    (y : (L.complex.X j').val.obj (op V.left)) :
    (assocHom hY hT hW x).app (j + j') kk hk V (hT.tmul j j' (op V.left) n y) =
      castHom W.complex.X (by omega) (op V.left)
        (hW.tmul (i + j) j' (op V.left)
          (hY.tmul i j (op V.left) (restrictAlong (P.complex.X i) V.hom x) n) y) := by
  rw [assocHom, transport_tmul, leftTmulHom_app, hW.tmul_castHom_left, castHom_castHom]

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- `t ↦ x ⊗ t` is additive in `x`. -/
theorem assocHom_add {i : ℤ} {U : C} (x x' : (P.complex.X i).val.obj (op U)) :
    assocHom hY hT hW (x + x') = assocHom hY hT hW x + assocHom hY hT hW x' := by
  simp only [assocHom, leftTmulHom_add, transport_add]

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- `t ↦ x ⊗ t` is compatible with restriction along a morphism of the site. -/
theorem assocHom_restrict {i : ℤ} {U U' : C} (q : U' ⟶ U)
    (x : (P.complex.X i).val.obj (op U)) :
    (assocHom hY hT hW x).restrict q = assocHom hY hT hW (restrictAlong (P.complex.X i) q x) := by
  simp only [assocHom, transport_restrict, leftTmulHom_restrict]

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The differential of `t ↦ x ⊗ t` is `t ↦ d x ⊗ t`. -/
theorem assocHom_diffAt {i : ℤ} {U : C} (x : (P.complex.X i).val.obj (op U)) :
    (assocHom hY hT hW x).diffAt =
      assocHom hY hT hW ((P.complex.d i (i + 1)).val.app (op U) x) := by
  simp only [assocHom, transport_diffAt, leftTmulHom_diffAt]



/-- `t ↦ x ⊗ t` is linear over the sheaf of rings in `x`. -/
theorem assocHom_smul {i : ℤ} {U : C} (r : R.obj.obj (op U))
    (x : (P.complex.X i).val.obj (op U)) :
    assocHom hY hT hW (r • x) = r • assocHom hY hT hW x := by
  have e : hY.leftTmulHom (r • x) = r • hY.leftTmulHom x := LocalHom.ext fun j k hjk V n => by
    rw [LocalHom.smul_app, leftTmulHom_app, leftTmulHom_app]
    rw [restrictAlong_smul, hY.tmul_smul_left, castHom_smul]
  simp only [assocHom, e, transport_smul]

/-- **The multiplication `x ⊗ t`** of a local section of `𝒫` with a local section of
`𝒩 ⊗_{𝒜'} ℒ`, with values in `(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ`: the value at `t` of `t ↦ x ⊗ t`. -/
noncomputable def assocTmul (i j : ℤ) (U : Cᵒᵖ) :
    (P.complex.X i).val.obj U →+ (T.complex.X j).val.obj U →+ (W.complex.X (i + j)).val.obj U :=
  AddMonoidHom.mk' (fun x => (castHom W.complex.X (add_comm j i) U).comp
      ((assocHom hY hT hW (U := U.unop) x).app j (j + i) rfl (Over.mk (𝟙 U.unop))))
    (fun x x' => by
      ext t
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.add_apply]
      rw [LocalHom.app_congr (assocHom_add hY hT hW (U := U.unop) x x'), LocalHom.add_app,
        map_add])

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- `x ⊗ t` is the value at `t` of the local homomorphism `t ↦ x ⊗ t`, transported to degree
`i + j`. -/
theorem assocTmul_apply (i j : ℤ) (U : Cᵒᵖ) (x : (P.complex.X i).val.obj U)
    (t : (T.complex.X j).val.obj U) :
    assocTmul hY hT hW i j U x t = castHom W.complex.X (add_comm j i) U
      ((assocHom hY hT hW (U := U.unop) x).app j (j + i) rfl (Over.mk (𝟙 U.unop)) t) :=
  rfl

/-- `(r x) ⊗ t = r (x ⊗ t)` for a local section `r` of the sheaf of rings. -/
theorem assocTmul_smul_left (i j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (x : (P.complex.X i).val.obj U) (t : (T.complex.X j).val.obj U) :
    assocTmul hY hT hW i j U (r • x) t = r • assocTmul hY hT hW i j U x t := by
  rw [assocTmul_apply, assocTmul_apply,
    LocalHom.app_congr (assocHom_smul hY hT hW (U := U.unop) r x), LocalHom.smul_app,
    castHom_smul]
  congr 2
  change (R.obj.map (𝟙 (op U.unop))) r = r
  rw [R.obj.map_id]
  rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- `x ⊗ (r t) = r (x ⊗ t)` for a local section `r` of the sheaf of rings. -/
theorem assocTmul_smul_right (i j : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (x : (P.complex.X i).val.obj U) (t : (T.complex.X j).val.obj U) :
    assocTmul hY hT hW i j U x (r • t) = r • assocTmul hY hT hW i j U x t := by
  rw [assocTmul_apply, assocTmul_apply,
    (assocHom hY hT hW (U := U.unop) x).map_smul j (j + i) rfl (Over.mk (𝟙 U.unop)) r t,
    castHom_smul]

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The multiplication `x ⊗ t` commutes with restriction of local sections. -/
theorem assocTmul_naturality (i j : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V)
    (x : (P.complex.X i).val.obj U) (t : (T.complex.X j).val.obj U) :
    (W.complex.X (i + j)).val.map g (assocTmul hY hT hW i j U x t) =
      assocTmul hY hT hW i j V ((P.complex.X i).val.map g x) ((T.complex.X j).val.map g t) := by
  rw [assocTmul_apply, castHom_naturality]
  refine Eq.trans ?_ (assocTmul_apply hY hT hW i j V _ _).symm
  congr 1
  have hA := (assocHom hY hT hW (U := U.unop) x).naturality j (j + i) rfl
    (Over.homMk g.unop (Category.comp_id g.unop) :
      Over.mk g.unop ⟶ Over.mk (𝟙 U.unop)) t
  refine hA.trans ?_
  refine ((assocHom hY hT hW (U := U.unop) x).toLocalGradedHom.app_mk_congr j (j + i) rfl
    (Category.id_comp g.unop).symm ((T.complex.X j).val.map g t)).trans ?_
  exact LocalHom.app_congr (assocHom_restrict hY hT hW g.unop x) j (j + i) rfl
    (Over.mk (𝟙 V.unop)) ((T.complex.X j).val.map g t)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- `(x ⊗ t) b = x ⊗ (t b)` for a local section `b` of `ℬ`. -/
theorem assocTmul_rightMul (i j p : ℤ) (U : Cᵒᵖ) (x : (P.complex.X i).val.obj U)
    (t : (T.complex.X j).val.obj U) (b : (B.complex.X p).val.obj U) :
    HEq ((W.mul (i + j) p).app U (assocTmul hY hT hW i j U x t) b)
      (assocTmul hY hT hW i (j + p) U x ((T.mul j p).app U t b)) := by
  rw [assocTmul_apply, assocTmul_apply, mul_app_castHom]
  refine (heq_castHom _ _ U _).trans (HEq.trans ?_ (heq_castHom _ _ U _).symm)
  refine HEq.trans (heq_of_eq ((assocHom hY hT hW (U := U.unop) x).isLinear j (j + i) rfl p
    (Over.mk (𝟙 U.unop)) t b).symm) ?_
  exact (assocHom hY hT hW (U := U.unop) x).app_heq _ _ _ _

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The Leibniz rule `d (x ⊗ t) = d x ⊗ t + (-1)^i x ⊗ d t` for `x` of degree `i`. -/
theorem assocTmul_d (i j : ℤ) (U : Cᵒᵖ) (x : (P.complex.X i).val.obj U)
    (t : (T.complex.X j).val.obj U) :
    (W.complex.d (i + j) (i + j + 1)).val.app U (assocTmul hY hT hW i j U x t) =
      gradedCast (fun q ↦ (W.complex.X q).val.obj U) (add_right_comm i 1 j)
          (assocTmul hY hT hW (i + 1) j U ((P.complex.d i (i + 1)).val.app U x) t) +
        (Int.negOnePow i : ℤ) •
          gradedCast (fun q ↦ (W.complex.X q).val.obj U) (add_assoc i j 1).symm
            (assocTmul hY hT hW i (j + 1) U x ((T.complex.d j (j + 1)).val.app U t)) := by
  rw [← castHom_apply, ← castHom_apply, assocTmul_apply, assocTmul_apply, assocTmul_apply,
    d_castHom_app W.complex (add_comm j i) (show j + i + 1 = i + j + 1 by omega)]
  have hd := LocalHom.diffAt_app (assocHom hY hT hW (U := U.unop) x) j (j + i + 1) (by omega)
    (Over.mk (𝟙 U.unop)) t
  rw [assocHom_diffAt] at hd
  rw [eq_sub_iff_add_eq] at hd
  refine (congrArg (castHom W.complex.X (show j + i + 1 = i + j + 1 by omega) U) hd.symm).trans ?_
  rw [map_add, map_zsmul, castHom_castHom, castHom_castHom]
  congr 1
  · exact castHom_heq _ _ _ _ ((assocHom hY hT hW _).app_heq _ _ _ _)
  · congr 1
    exact castHom_heq _ _ _ _ ((assocHom hY hT hW _).app_heq _ _ _ _)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- `n ↦ (x a) ⊗ n` is `n ↦ x ⊗ (a n)`: the multiplication map is balanced. -/
theorem leftTmulHom_mul {i p : ℤ} {U : C} (x : (P.complex.X i).val.obj (op U))
    (b : (A.complex.X p).val.obj (op U)) (h : p + i = i + p) :
    hY.leftTmulHom ((P.mul i p).app (op U) x b) =
      (N.leftStructure.leftMulHom b).comp (hY.leftTmulHom x) h :=
  LocalHom.ext fun j k hjk W n => by
    rw [LocalHom.comp_app _ _ h (show j + p = j + p from rfl) (show j + p + i = k by omega),
      leftTmulHom_app, leftTmulHom_app, DifferentialGradedBimodule.LeftStructure.leftMulHom_app]
    have hmul : restrictAlong (P.complex.X (i + p)) W.hom ((P.mul i p).app (op U) x b) =
        (P.mul i p).app (op W.left) (restrictAlong (P.complex.X i) W.hom x)
          (restrictAlong (A.complex.X p) W.hom b) :=
      (P.mul i p).naturality W.hom.op x b
    rw [hmul]
    refine castHom_heq Y.complex.X _ _ _ ((hY.tmul_balanced i p j (op W.left) _ _ n).trans ?_)
    exact hY.tmul_heq rfl (by omega) _ HEq.rfl (heq_castHom _ _ _ _).symm

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- `t ↦ (x a) ⊗ t` is `t ↦ x ⊗ (a t)`. -/
theorem assocHom_mul {i p : ℤ} {U : C} (x : (P.complex.X i).val.obj (op U))
    (b : (A.complex.X p).val.obj (op U)) (h : p + i = i + p) :
    assocHom hY hT hW ((P.mul i p).app (op U) x b) =
      (hT.transport hT (N.leftStructure.leftMulHom b)).comp (assocHom hY hT hW x) h := by
  simp only [assocHom, leftTmulHom_mul hY x b h, transport_comp hT hT hW]

/-- `(x a) ⊗ t = x ⊗ (a t)`. -/
theorem assocTmul_balanced (i p j : ℤ) (U : Cᵒᵖ) (x : (P.complex.X i).val.obj U)
    (b : (A.complex.X p).val.obj U) (t : (T.complex.X j).val.obj U) :
    HEq (assocTmul hY hT hW (i + p) j U ((P.mul i p).app U x b) t)
      (assocTmul hY hT hW i (p + j) U x
        (((hT.leftStructure N.leftStructure).leftMul p j).app U b t)) := by
  rw [assocTmul_apply, assocTmul_apply,
    IsTensorProduct.leftStructure_leftMul_eq hT N.leftStructure p j U.unop b t,
    LocalHom.app_congr (assocHom_mul hY hT hW (U := U.unop) x b (by omega)),
    LocalHom.comp_app _ _ (show p + i = i + p by omega) (show j + p = j + p from rfl)
      (show j + p + i = j + (i + p) by omega)]
  refine (heq_castHom _ _ U _).trans (HEq.trans ?_ (heq_castHom _ _ U _).symm)
  refine ((assocHom hY hT hW (U := U.unop) x).app_heq _
    (show j + p + i = p + j + i by omega) _ _).trans ?_
  exact heq_of_eq (LocalGradedHom.app_heq_congr _ (by omega : j + p = p + j) _ _ _
    (heq_castHom _ _ _ _).symm)

end IsTensorProduct

open DifferentialGradedBimodule in
/-- The multiplication `x ⊗ t` and its laws: `(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ` carries the structure of a
tensor product of `𝒫` with `𝒩 ⊗_{𝒜'} ℒ`, except for the universal property. -/
noncomputable def IsTensorProduct.assocCore :
    IsTensorProductCore P (ofLeftStructure (hT.leftStructure N.leftStructure)) W where
  tmul := assocTmul hY hT hW
  tmul_smul_left := assocTmul_smul_left hY hT hW
  tmul_smul_right := assocTmul_smul_right hY hT hW
  tmul_naturality := assocTmul_naturality hY hT hW
  tmul_balanced := assocTmul_balanced hY hT hW
  tmul_rightMul := assocTmul_rightMul hY hT hW
  tmul_d := assocTmul_d hY hT hW

namespace IsTensorProduct

end IsTensorProduct

end Assoc

end Generic

/-! ### The universal property -/

section Universal

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]
  {A A' B : DifferentialGradedAlgebra.{u, u} R} {P : DifferentialGradedModule.{u, u, u} A}
  {N : DifferentialGradedBimodule.{u, u, u} A A'} {L : DifferentialGradedBimodule.{u, u, u} A' B}
  {Y : DifferentialGradedModule.{u, u, u} A'} {T W : DifferentialGradedModule.{u, u, u} B}
  (hY : IsTensorProduct P N Y) (hT : IsTensorProduct N.toRightModule L T)
  (hW : IsTensorProduct Y L W)

namespace IsTensorProduct

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- `(x ⊗ n) ⊗ y = x ⊗ (n ⊗ y)`, read through a local homomorphism out of
`(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ`. -/
theorem app_tmul_tmul {L' : DifferentialGradedModule.{u, u, u} B} {n : ℤ} {U : C}
    (φ : LocalHom W L' n U) (i j j' k : ℤ) (hk : i + j + j' + n = k) (V : Over U)
    (x : (P.complex.X i).val.obj (op V.left)) (m : (N.complex.X j).val.obj (op V.left))
    (y : (L.complex.X j').val.obj (op V.left)) :
    φ.app (i + j + j') k hk V (hW.tmul (i + j) j' (op V.left) (hY.tmul i j (op V.left) x m) y) =
      φ.app (i + (j + j')) k (by omega) V
        (assocTmul hY hT hW i (j + j') (op V.left) x (hT.tmul j j' (op V.left) m y)) := by
  refine LocalGradedHom.app_heq_congr φ.toLocalGradedHom (by omega) _ _ V ?_
  rw [assocTmul_apply]
  refine HEq.trans ?_ (heq_castHom _ _ _ _).symm
  refine HEq.trans ?_ (heq_of_eq (assocHom_tmul hY hT hW (U := V.left) x j j' (j + j' + i) rfl
    (Over.mk (𝟙 V.left)) m y)).symm
  refine HEq.trans ?_ (heq_castHom _ _ _ _).symm
  rw [show (Over.mk (𝟙 V.left)).hom = 𝟙 V.left from rfl, restrictAlong_id]
  exact HEq.rfl

/-- **A local homomorphism out of `(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ` is determined by its values on the local
sections `x ⊗ t`**, `x` a local section of `𝒫` and `t` one of `𝒩 ⊗_{𝒜'} ℒ`. -/
theorem assoc_localHom_ext {L' : DifferentialGradedModule.{u, u, u} B} {n : ℤ} {U : C}
    {f g : LocalHom W L' n U}
    (h : ∀ (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (P.complex.X i).val.obj (op V.left)) (t : (T.complex.X j).val.obj (op V.left)),
      f.app (i + j) k hijk V (assocTmul hY hT hW i j (op V.left) x t) =
        g.app (i + j) k hijk V (assocTmul hY hT hW i j (op V.left) x t)) :
    f = g := by
  let hH := isSheafHom_sheafHomModule L L'
  apply (hW.universal L' n U).injective
  rw [← toBalancedDg_ofBalancedDg hH (hW.universal L' n U f),
    ← toBalancedDg_ofBalancedDg hH (hW.universal L' n U g)]
  congr 1
  refine hY.localHom_ext fun i j k hijk V x m => ?_
  refine hH.isInternalHom.sections_ext fun j' k' hj'k' W' y => ?_
  have hn : restrictAlong (Y.complex.X (i + j)) W'.hom (hY.tmul i j (op V.left) x m) =
      hY.tmul i j (op W'.left) (restrictAlong (P.complex.X i) W'.hom x)
        (restrictAlong (N.complex.X j) W'.hom m) :=
    hY.tmul_naturality i j W'.hom.op x m
  have key : ∀ φ : LocalHom W L' n U,
      (hH.isInternalHom.sectionsEquiv k V.left
        ((ofBalancedDg hH (hW.universal L' n U φ)).app (i + j) k hijk V
          (hY.tmul i j (op V.left) x m))).app j' k' hj'k' W' y =
      φ.app (i + (j + j')) k' (by omega) (Over.mk (W'.hom ≫ V.hom))
        (assocTmul hY hT hW i (j + j') (op W'.left) (restrictAlong (P.complex.X i) W'.hom x)
          (hT.tmul j j' (op W'.left) (restrictAlong (N.complex.X j) W'.hom m) y)) := by
    intro φ
    refine (ofBalancedDg_sectionsEquiv_app hH _ (i + j) k hijk V _ j' k' hj'k' W' y).trans ?_
    refine (hW.universal_app L' n U φ (i + j) j' k' (by omega) (Over.mk (W'.hom ≫ V.hom))
      (restrictAlong (Y.complex.X (i + j)) W'.hom (hY.tmul i j (op V.left) x m)) y).trans ?_
    rw [hn]
    exact app_tmul_tmul hY hT hW φ i j j' k' (by omega) (Over.mk (W'.hom ≫ V.hom)) _ _ y
  exact (key f).trans ((h _ _ _ _ _ _ _).trans (key g).symm)

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- A balanced bilinear family respects an equality in its first variable and a heterogeneous
equality in its second. -/
theorem _root_.SheafOfModules.LocalBalancedBilinear.app_congr_heq
    {M : DifferentialGradedModule.{u, u, u} A} {N' : DifferentialGradedBimodule.{u, u, u} A B}
    {L' : DifferentialGradedModule.{u, u, u} B} {n : ℤ} {U : C}
    (β : LocalBalancedBilinear M N' L' n U) {i j j' k : ℤ} (hijk : i + j + n = k)
    (hijk' : i + j' + n = k) (V : Over U) {x x' : (M.complex.X i).val.obj (op V.left)}
    (hx : x = x') {y : (N'.complex.X j).val.obj (op V.left)}
    {y' : (N'.complex.X j').val.obj (op V.left)} (hj : j = j') (hy : HEq y y') :
    β.app i j k hijk V x y = β.app i j' k hijk' V x' y' := by
  subst hx hj
  rw [eq_of_heq hy]

section Surjective

open DifferentialGradedBimodule

variable {L' : DifferentialGradedModule.{u, u, u} B} {n : ℤ} {U : C}
  (β : LocalBalancedBilinear P (ofLeftStructure (hT.leftStructure N.leftStructure)) L' n U)

/-- For local sections `x` of `𝒫` and `m` of `𝒩`, the local homomorphism `y ↦ β(x, m ⊗ y)` out
of `ℒ`. -/
noncomputable def assocCurry {i j k : ℤ} (hijk : i + j + n = k) (V : Over U)
    (x : (P.complex.X i).val.obj (op V.left)) (m : (N.complex.X j).val.obj (op V.left)) :
    LocalHom L.toRightModule L' k V.left :=
  (hT.leftTmulHom m).comp (balancedHomDg β (rfl : i + n = i + n) V x) (by omega)

/-- The value of `y ↦ β(x, m ⊗ y)` at a local section `y` of `ℒ` over `W` is `β` applied to the
restriction of `x` and to the tensor product of the restriction of `m` with `y`. -/
theorem assocCurry_app {i j k : ℤ} (hijk : i + j + n = k) (V : Over U)
    (x : (P.complex.X i).val.obj (op V.left)) (m : (N.complex.X j).val.obj (op V.left))
    (j' k' : ℤ) (hj'k' : j' + k = k') (W : Over V.left)
    (y : (L.complex.X j').val.obj (op W.left)) :
    (assocCurry hT β hijk V x m).app j' k' hj'k' W y =
      β.app i (j' + j) k' (by omega) (Over.mk (W.hom ≫ V.hom))
        (restrictAlong (P.complex.X i) W.hom x)
        (castHom T.complex.X (add_comm j j') (op W.left)
          (hT.tmul j j' (op W.left) (restrictAlong (N.complex.X j) W.hom m) y)) :=
  congrArg (β.app i (j' + j) k' (by omega) (Over.mk (W.hom ≫ V.hom))
    (restrictAlong (P.complex.X i) W.hom x)) (leftTmulHom_app hT m j' (j' + j) rfl W y)

/-- `y ↦ β(x, m ⊗ y)` is additive in `x`. -/
theorem assocCurry_add_left {i j k : ℤ} (hijk : i + j + n = k) (V : Over U)
    (x x' : (P.complex.X i).val.obj (op V.left)) (m : (N.complex.X j).val.obj (op V.left))
    (j' k' : ℤ) (hj'k' : j' + k = k') (W : Over V.left)
    (y : (L.complex.X j').val.obj (op W.left)) :
    (assocCurry hT β hijk V (x + x') m).app j' k' hj'k' W y =
      (assocCurry hT β hijk V x m).app j' k' hj'k' W y +
        (assocCurry hT β hijk V x' m).app j' k' hj'k' W y := by
  rw [assocCurry_app, assocCurry_app, assocCurry_app, restrictAlong_add, map_add]
  rfl

/-- `y ↦ β(x, m ⊗ y)` is additive in `m`. -/
theorem assocCurry_add_right {i j k : ℤ} (hijk : i + j + n = k) (V : Over U)
    (x : (P.complex.X i).val.obj (op V.left)) (m m' : (N.complex.X j).val.obj (op V.left))
    (j' k' : ℤ) (hj'k' : j' + k = k') (W : Over V.left)
    (y : (L.complex.X j').val.obj (op W.left)) :
    (assocCurry hT β hijk V x (m + m')).app j' k' hj'k' W y =
      (assocCurry hT β hijk V x m).app j' k' hj'k' W y +
        (assocCurry hT β hijk V x m').app j' k' hj'k' W y := by
  rw [assocCurry_app, assocCurry_app, assocCurry_app, restrictAlong_add, hT.tmul_add_left,
    castHom_add]
  exact map_add _ _ _

/-- `y ↦ β(r x, m ⊗ y)` is `r` times `y ↦ β(x, m ⊗ y)`. -/
theorem assocCurry_smul_left {i j k : ℤ} (hijk : i + j + n = k) (V : Over U)
    (r : R.obj.obj (op V.left)) (x : (P.complex.X i).val.obj (op V.left))
    (m : (N.complex.X j).val.obj (op V.left)) (j' k' : ℤ) (hj'k' : j' + k = k')
    (W : Over V.left) (y : (L.complex.X j').val.obj (op W.left)) :
    (assocCurry hT β hijk V (r • x) m).app j' k' hj'k' W y =
      R.obj.map W.hom.op r • (assocCurry hT β hijk V x m).app j' k' hj'k' W y := by
  rw [assocCurry_app, assocCurry_app, restrictAlong_smul]
  exact β.map_smul_left _ _ _ _ _ _ _ _

/-- `y ↦ β(x, (r m) ⊗ y)` is `r` times `y ↦ β(x, m ⊗ y)`. -/
theorem assocCurry_smul_right {i j k : ℤ} (hijk : i + j + n = k) (V : Over U)
    (r : R.obj.obj (op V.left)) (x : (P.complex.X i).val.obj (op V.left))
    (m : (N.complex.X j).val.obj (op V.left)) (j' k' : ℤ) (hj'k' : j' + k = k')
    (W : Over V.left) (y : (L.complex.X j').val.obj (op W.left)) :
    (assocCurry hT β hijk V x (r • m)).app j' k' hj'k' W y =
      R.obj.map W.hom.op r • (assocCurry hT β hijk V x m).app j' k' hj'k' W y := by
  rw [assocCurry_app, assocCurry_app, restrictAlong_smul, hT.tmul_smul_left, castHom_smul]
  exact β.map_smul_right _ _ _ _ _ _ _ _

/-- `y ↦ β(x, m ⊗ y)` is compatible with restriction along a morphism over `U`. -/
theorem assocCurry_restrict {i j k : ℤ} (hijk : i + j + n = k) {V V' : Over U} (q : V' ⟶ V)
    (x : (P.complex.X i).val.obj (op V.left)) (m : (N.complex.X j).val.obj (op V.left)) :
    (assocCurry hT β hijk V x m).restrict q.left =
      assocCurry hT β hijk V' (restrictAlong (P.complex.X i) q.left x)
        (restrictAlong (N.complex.X j) q.left m) :=
  LocalHom.ext fun j' k' hj'k' W y => by
    change (assocCurry hT β hijk V x m).app j' k' hj'k' (Over.mk (W.hom ≫ q.left)) y = _
    rw [assocCurry_app, assocCurry_app, restrictAlong_comp, restrictAlong_comp]
    exact β.app_mk_congr i (j' + j) k' _
      (show (W.hom ≫ q.left) ≫ V.hom = W.hom ≫ V'.hom by rw [Category.assoc, Over.w q]) _ _

/-- **The balanced family on `𝒫 × 𝒩` with values in `SheafHom^dg_ℬ(ℒ, ℒ')`** attached to a
balanced family `β` on `𝒫 × (𝒩 ⊗_{𝒜'} ℒ)`: `(x, m) ↦ (y ↦ β(x, m ⊗ y))`. -/
noncomputable def assocFamily : LocalBalancedBilinear P N (sheafHomModule L L') n U where
  app i j k hijk V := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun m =>
      ((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv k V.left).symm
        (assocCurry hT β hijk V x m))
      (fun m m' => (isSheafHom_sheafHomModule L L').isInternalHom.symm_add k V.left _ _ _
        fun j' k' hj'k' W y => assocCurry_add_right hT β hijk V x m m' j' k' hj'k' W y))
    (fun x x' => AddMonoidHom.ext fun m =>
      (isSheafHom_sheafHomModule L L').isInternalHom.symm_add k V.left _ _ _
        fun j' k' hj'k' W y => assocCurry_add_left hT β hijk V x x' m j' k' hj'k' W y)
  map_smul_left i j k hijk V r x m :=
    (isSheafHom_sheafHomModule L L').isInternalHom.symm_smul k V.left r _ _
      fun j' k' hj'k' W y => assocCurry_smul_left hT β hijk V r x m j' k' hj'k' W y
  map_smul_right i j k hijk V r x m :=
    (isSheafHom_sheafHomModule L L').isInternalHom.symm_smul k V.left r _ _
      fun j' k' hj'k' W y => assocCurry_smul_right hT β hijk V r x m j' k' hj'k' W y
  naturality i j k hijk {V V'} q x m := by
    change ((sheafHomModule L L').complex.X k).val.map q.left.op
        (((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv k V.left).symm
          (assocCurry hT β hijk V x m)) =
      ((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv k V'.left).symm
        (assocCurry hT β hijk V' (restrictAlong (P.complex.X i) q.left x)
          (restrictAlong (N.complex.X j) q.left m))
    rw [← assocCurry_restrict, (isSheafHom_sheafHomModule L L').isInternalHom.symm_naturality]
  balanced i p j k hijk V x b m := by
    change ((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv k V.left).symm
        (assocCurry hT β hijk V ((P.mul i p).app (op V.left) x b) m) =
      ((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv k V.left).symm
        (assocCurry hT β (by omega) V x ((N.leftMul p j).app (op V.left) b m))
    congr 1
    refine LocalHom.ext fun j' k' hj'k' W y => ?_
    rw [assocCurry_app, assocCurry_app]
    have hx : restrictAlong (P.complex.X (i + p)) W.hom ((P.mul i p).app (op V.left) x b) =
        (P.mul i p).app (op W.left) (restrictAlong (P.complex.X i) W.hom x)
          (restrictAlong (A.complex.X p) W.hom b) :=
      (P.mul i p).naturality W.hom.op x b
    have hm : restrictAlong (N.complex.X (p + j)) W.hom ((N.leftMul p j).app (op V.left) b m) =
        (N.leftMul p j).app (op W.left) (restrictAlong (A.complex.X p) W.hom b)
          (restrictAlong (N.complex.X j) W.hom m) :=
      (N.leftMul p j).naturality W.hom.op b m
    rw [hx, hm]
    refine (β.balanced i p (j' + j) k' (by omega) _ _ _ _).trans ?_
    refine β.app_heq_right _ _ _ _ (by omega) ?_
    have e : ∀ {d d' : ℤ} (hd : d = d') {z : (T.complex.X d).val.obj (op W.left)}
        {z' : (T.complex.X d').val.obj (op W.left)}, HEq z z' →
        HEq (((hT.leftStructure N.leftStructure).leftMul p d).app (op W.left)
            (restrictAlong (A.complex.X p) W.hom b) z)
          (((hT.leftStructure N.leftStructure).leftMul p d').app (op W.left)
            (restrictAlong (A.complex.X p) W.hom b) z') := by
      intro d d' hd z z' hz
      subst hd
      rw [eq_of_heq hz]
    refine (e (show j' + j = j + j' by omega) (heq_castHom _ _ _ _)).trans ?_
    refine (IsTensorProduct.leftStructure_leftMul_tmul hT N.leftStructure p j j' (op W.left)
      _ _ y).trans ?_
    exact (heq_castHom _ _ _ _).symm
  map_rightMul i j p k hijk V x m b := by
    refine (isSheafHom_sheafHomModule L L').isInternalHom.sections_ext
      fun j' k' hj'k' W y => ?_
    rw [(isSheafHom_sheafHomModule L L').mul_spec]
    change (((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv (k + p) V.left)
        (((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv (k + p) V.left).symm
          (assocCurry hT β (by omega) V x ((N.rightMul j p).app (op V.left) m b)))).app
          j' k' hj'k' W y =
      (((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv k V.left)
        (((isSheafHom_sheafHomModule L L').isInternalHom.sectionsEquiv k V.left).symm
          (assocCurry hT β hijk V x m))).app (p + j') k' (by omega) W _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, assocCurry_app, assocCurry_app]
    refine β.app_heq_right _ _ _ _ (by omega) ?_
    have hm : restrictAlong (N.complex.X (j + p)) W.hom ((N.rightMul j p).app (op V.left) m b) =
        (N.rightMul j p).app (op W.left) (restrictAlong (N.complex.X j) W.hom m)
          (restrictAlong (A'.complex.X p) W.hom b) :=
      (N.rightMul j p).naturality W.hom.op m b
    rw [hm]
    refine (heq_castHom _ _ _ _).trans (HEq.trans ?_ (heq_castHom _ _ _ _).symm)
    exact hT.tmul_balanced j p j' (op W.left) _ _ y

/-- **Every balanced family on `𝒫 × (𝒩 ⊗_{𝒜'} ℒ)` comes from a local homomorphism out of
`(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ`.** -/
theorem exists_localHom_assocTmul :
    ∃ f : LocalHom W L' n U, ∀ (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
      (x : (P.complex.X i).val.obj (op V.left)) (t : (T.complex.X j).val.obj (op V.left)),
      f.app (i + j) k hijk V (assocTmul hY hT hW i j (op V.left) x t) = β.app i j k hijk V x t := by
  let hH := isSheafHom_sheafHomModule L L'
  let g := (hY.universal (sheafHomModule L L') n U).symm (assocFamily hT β)
  let f := (hW.universal L' n U).symm (toBalancedDg hH g)
  refine ⟨f, fun i j k hijk V x t => ?_⟩
  have hΦ : (assocHom hY hT hW x).comp (f.restrict V.hom) (rfl : i + n = i + n) =
      balancedHomDg β (rfl : i + n = i + n) V x := by
    refine hT.localHom_ext fun j' j'' k' hk' W m y => ?_
    have e₁ : ((assocHom hY hT hW x).comp (f.restrict V.hom) (rfl : i + n = i + n)).app
          (j' + j'') k' hk' W (hT.tmul j' j'' (op W.left) m y) =
        f.app (i + j' + j'') k' (by omega) (Over.mk (W.hom ≫ V.hom))
          (hW.tmul (i + j') j'' (op W.left)
            (hY.tmul i j' (op W.left) (restrictAlong (P.complex.X i) W.hom x) m) y) := by
      rw [LocalHom.comp_app _ _ _ (show j' + j'' + i = j' + j'' + i from rfl)
        (show j' + j'' + i + n = k' by omega)]
      change f.app (j' + j'' + i) k' _ (Over.mk (W.hom ≫ V.hom))
        ((assocHom hY hT hW x).app (j' + j'') (j' + j'' + i) rfl W
          (hT.tmul j' j'' (op W.left) m y)) = _
      rw [assocHom_tmul]
      exact f.toLocalGradedHom.app_castHom_source _ _ _ _ _
    have e₂ : f.app (i + j' + j'') k' (by omega) (Over.mk (W.hom ≫ V.hom))
          (hW.tmul (i + j') j'' (op W.left)
            (hY.tmul i j' (op W.left) (restrictAlong (P.complex.X i) W.hom x) m) y) =
        (assocCurry hT β (show i + j' + n = i + j' + n from rfl) (Over.mk (W.hom ≫ V.hom))
          (restrictAlong (P.complex.X i) W.hom x) m).app j'' k' (by omega)
          (Over.mk (𝟙 W.left)) y := by
      refine (hW.universal_app L' n U f (i + j') j'' k' (by omega) (Over.mk (W.hom ≫ V.hom))
        _ y).symm.trans ?_
      have e₃ : g.app (i + j') (i + j' + n) rfl (Over.mk (W.hom ≫ V.hom))
            (hY.tmul i j' (op W.left) (restrictAlong (P.complex.X i) W.hom x) m) =
          (hH.isInternalHom.sectionsEquiv (i + j' + n) W.left).symm
            (assocCurry hT β (show i + j' + n = i + j' + n from rfl) (Over.mk (W.hom ≫ V.hom))
              (restrictAlong (P.complex.X i) W.hom x) m) :=
        (hY.universal_app (sheafHomModule L L') n U g i j' (i + j' + n) rfl
          (Over.mk (W.hom ≫ V.hom)) _ m).symm.trans
          (congrArg (fun γ => LocalBalancedBilinear.app γ i j' (i + j' + n) rfl
            (Over.mk (W.hom ≫ V.hom)) (restrictAlong (P.complex.X i) W.hom x) m)
            (Equiv.apply_symm_apply _ _))
      rw [Equiv.apply_symm_apply, toBalancedDg_app, balancedValDg_eq, e₃]
      exact congrArg (fun φ : LocalHom L.toRightModule L' (i + j' + n) W.left =>
        φ.app j'' k' (by omega) (Over.mk (𝟙 W.left)) y) (Equiv.apply_symm_apply _ _)
    rw [e₁, e₂, assocCurry_app, balancedHomDg_eq]
    refine (β.app_mk_congr i (j'' + j') k' _ (Category.id_comp (W.hom ≫ V.hom)) _ _).trans ?_
    refine β.app_congr_heq _ _ _ (restrictAlong_id _ _) (by omega) ?_
    refine (heq_castHom _ _ _ _).trans ?_
    exact heq_of_eq (congrArg (fun z => hT.tmul j' j'' (op W.left) z y) (restrictAlong_id _ m))
  have h₁ := LocalHom.app_congr hΦ j k (show j + (i + n) = k by omega) (Over.mk (𝟙 V.left)) t
  rw [balancedHomDg_eq, LocalHom.comp_app _ _ _ (show j + i = j + i from rfl)
    (show j + i + n = k by omega)] at h₁
  refine Eq.trans ?_ (h₁.trans (β.app_top i j k hijk V x t))
  rw [assocTmul_apply]
  refine (f.toLocalGradedHom.app_castHom_source (add_comm j i) (by omega) hijk V _).trans ?_
  change _ = f.app (j + i) k _ (Over.mk (𝟙 V.left ≫ V.hom)) _
  exact (f.toLocalGradedHom.app_mk_congr _ _ _ (Category.id_comp V.hom) _).symm

end Surjective

open DifferentialGradedBimodule in
/-- **`(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ` is the tensor product of `𝒫` and `𝒩 ⊗_{𝒜'} ℒ`**, with
multiplication map `x ⊗ t`. -/
noncomputable def assoc :
    IsTensorProduct P (ofLeftStructure (hT.leftStructure N.leftStructure)) W :=
  (assocCore hY hT hW).toIsTensorProduct
    (fun _ _ _ => Equiv.ofBijective (fun f => (assocCore hY hT hW).compBalanced f)
      ⟨fun _ _ hfg => assoc_localHom_ext hY hT hW fun i j k hijk V x t =>
          congrArg (fun β => LocalBalancedBilinear.app β i j k hijk V x t) hfg,
        fun β => by
          obtain ⟨f, hf⟩ := exists_localHom_assocTmul hY hT hW β
          exact ⟨f, LocalBalancedBilinear.ext fun i j k hijk V x t => hf i j k hijk V x t⟩⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- The multiplication map of `assoc` is `assocTmul`. -/
theorem assoc_tmul (i j : ℤ) (U : Cᵒᵖ) (x : (P.complex.X i).val.obj U)
    (t : (T.complex.X j).val.obj U) :
    (assoc hY hT hW).tmul i j U x t = assocTmul hY hT hW i j U x t := rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- A morphism of complexes commutes with transport of local sections along an equality of
degrees. -/
theorem hom_f_castHom {K K' : CochainComplex (SheafOfModules.{u} R) ℤ} (φ : K ⟶ K') {a b : ℤ}
    (h : a = b) (U : Cᵒᵖ) (z : (K.X a).val.obj U) :
    (φ.f b).val.app U (castHom K.X h U z) = castHom K'.X h U ((φ.f a).val.app U z) := by
  subst h; rfl

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- The comparison of two tensor products of the same pair sends `x ⊗ y` to `x ⊗ y`. -/
theorem uniqueIso_hom_tmul {M : DifferentialGradedModule.{u, u, u} A'}
    {T₁ T₂ : DifferentialGradedModule.{u, u, u} B} (h₁ : IsTensorProduct M L T₁)
    (h₂ : IsTensorProduct M L T₂) (i j : ℤ) (U : Cᵒᵖ) (x : (M.complex.X i).val.obj U)
    (y : (L.complex.X j).val.obj U) :
    ((h₁.uniqueIso h₂).hom.toHomologicalComplex.f (i + j)).val.app U (h₁.tmul i j U x y) =
      h₂.tmul i j U x y :=
  h₁.descend_tmul h₂ U.unop i j (i + j) (add_zero (i + j)) (Over.mk (𝟙 U.unop)) x y

omit [∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)] in
/-- A morphism of differential graded modules carries `x ⊗ t` to `x' ⊗ t` as soon as it carries
`(x ⊗ n) ⊗ y` to `(x' ⊗ n) ⊗ y`. -/
theorem map_assocTmul {P' : DifferentialGradedModule.{u, u, u} A}
    {Y' : DifferentialGradedModule.{u, u, u} A'} {W' : DifferentialGradedModule.{u, u, u} B}
    (hY' : IsTensorProduct P' N Y') (hW' : IsTensorProduct Y' L W') (G : W ⟶ W') {i : ℤ}
    {U : C} (x : (P.complex.X i).val.obj (op U)) (x' : (P'.complex.X i).val.obj (op U))
    (hG : ∀ (j j' : ℤ) (V : Over U) (n : (N.complex.X j).val.obj (op V.left))
      (y : (L.complex.X j').val.obj (op V.left)),
      (G.toHomologicalComplex.f (i + j + j')).val.app (op V.left)
          (hW.tmul (i + j) j' (op V.left)
            (hY.tmul i j (op V.left) (restrictAlong (P.complex.X i) V.hom x) n) y) =
        hW'.tmul (i + j) j' (op V.left)
          (hY'.tmul i j (op V.left) (restrictAlong (P'.complex.X i) V.hom x') n) y)
    (j : ℤ) (t : (T.complex.X j).val.obj (op U)) :
    (G.toHomologicalComplex.f (i + j)).val.app (op U) (assocTmul hY hT hW i j (op U) x t) =
      assocTmul hY' hT hW' i j (op U) x' t := by
  have key : (assocHom hY hT hW x).comp (LocalHom.ofHom G U) (add_zero i) =
      assocHom hY' hT hW' x' := hT.localHom_ext fun j₁ j₂ k hk V n y => by
    rw [LocalHom.comp_app _ _ _ (show j₁ + j₂ + i = j₁ + j₂ + i from rfl)
      (show j₁ + j₂ + i + 0 = k by omega), assocHom_tmul, assocHom_tmul, LocalHom.ofHom_app,
      hom_f_castHom, castHom_castHom, hG]
  rw [assocTmul_apply, assocTmul_apply, hom_f_castHom]
  congr 1
  have e := LocalHom.app_congr key j (j + i) (by omega) (Over.mk (𝟙 U)) t
  rw [LocalHom.comp_app _ _ _ rfl (show j + i + 0 = j + i by omega), LocalHom.ofHom_app,
    castHom_self] at e
  exact e

end IsTensorProduct

end Universal

/-! ### Associativity of the tensor product functors -/

section Functor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}}
  {A A' B : DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}
  (N : DifferentialGradedBimodule.{u, u, u} A A') (L : DifferentialGradedBimodule.{u, u, u} A' B)

namespace RelativeTensor

/-- **The tensor product `𝒩 ⊗_{𝒜'} ℒ` of a differential graded `(𝒜, 𝒜')`-bimodule with a
differential graded `(𝒜', ℬ)`-bimodule**, a differential graded `(𝒜, ℬ)`-bimodule. -/
noncomputable def bimoduleTensor : DifferentialGradedBimodule.{u, u, u} A B :=
  DifferentialGradedBimodule.ofLeftStructure
    ((isTensorProductDgTensorRight N.toRightModule L).leftStructure N.leftStructure)

/-- The right differential graded `ℬ`-module underlying `𝒩 ⊗_{𝒜'} ℒ` is the tensor product of
`𝒩`, read as a right differential graded `𝒜'`-module, with `ℒ`. -/
theorem bimoduleTensor_toRightModule :
    (bimoduleTensor N L).toRightModule = dgTensorRight N.toRightModule L := rfl

/-- **Associativity of the tensor product**: `(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ ≅ 𝒫 ⊗_𝒜 (𝒩 ⊗_{𝒜'} ℒ)`, by
`(x ⊗ n) ⊗ y ↦ x ⊗ (n ⊗ y)`. -/
noncomputable def dgTensorAssocIso (P : DifferentialGradedModule.{u, u, u} A) :
    dgTensorRight (dgTensorRight P N) L ≅ dgTensorRight P (bimoduleTensor N L) :=
  (IsTensorProduct.assoc (isTensorProductDgTensorRight P N)
      (isTensorProductDgTensorRight N.toRightModule L)
      (isTensorProductDgTensorRight (dgTensorRight P N) L)).uniqueIso
    (isTensorProductDgTensorRight P (bimoduleTensor N L))

/-- **Associativity of the tensor product, naturally**: the functors
`(- ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ` and `- ⊗_𝒜 (𝒩 ⊗_{𝒜'} ℒ)` of right differential graded `𝒜`-modules are
isomorphic. -/
noncomputable def dgTensorAssocNatIso :
    dgTensorRightFunctor N ⋙ dgTensorRightFunctor L ≅
      dgTensorRightFunctor (bimoduleTensor N L) :=
  NatIso.ofComponents (dgTensorAssocIso N L) fun {P P'} p => by
    refine (IsTensorProduct.assoc (isTensorProductDgTensorRight P N)
      (isTensorProductDgTensorRight N.toRightModule L)
      (isTensorProductDgTensorRight (dgTensorRight P N) L)).hom_ext_tmul fun i j U x t => ?_
    simp only [DifferentialGradedModule.comp_f]
    change ((dgTensorAssocIso N L P').hom.toHomologicalComplex.f (i + j)).val.app (op U)
        ((((dgTensorRightFunctor N ⋙ dgTensorRightFunctor L).map p).toHomologicalComplex.f
          (i + j)).val.app (op U) (IsTensorProduct.assocTmul _ _ _ i j (op U) x t)) =
      (((dgTensorRightFunctor (bimoduleTensor N L)).map p).toHomologicalComplex.f
          (i + j)).val.app (op U)
        (((dgTensorAssocIso N L P).hom.toHomologicalComplex.f (i + j)).val.app (op U)
          (IsTensorProduct.assocTmul _ _ _ i j (op U) x t))
    have hG : ∀ (j₁ j₂ : ℤ) (V : Over U) (n : (N.complex.X j₁).val.obj (op V.left))
        (y : (L.complex.X j₂).val.obj (op V.left)),
        (((dgTensorRightFunctor N ⋙ dgTensorRightFunctor L).map p).toHomologicalComplex.f
            (i + j₁ + j₂)).val.app (op V.left)
          ((isTensorProductDgTensorRight (dgTensorRight P N) L).tmul (i + j₁) j₂ (op V.left)
            ((isTensorProductDgTensorRight P N).tmul i j₁ (op V.left)
              (restrictAlong (P.complex.X i) V.hom x) n) y) =
        (isTensorProductDgTensorRight (dgTensorRight P' N) L).tmul (i + j₁) j₂ (op V.left)
          ((isTensorProductDgTensorRight P' N).tmul i j₁ (op V.left)
            (restrictAlong (P'.complex.X i) V.hom ((p.toHomologicalComplex.f i).val.app (op U) x))
            n) y := by
      intro j₁ j₂ V n y
      refine ((tensorFunctorDataDgTensorRight L).map_spec
        ((dgTensorRightFunctor N).map p) (i + j₁) j₂ (op V.left) _ y).trans ?_
      refine congrArg (fun z => (isTensorProductDgTensorRight (dgTensorRight P' N) L).tmul
        (i + j₁) j₂ (op V.left) z y) ?_
      refine ((tensorFunctorDataDgTensorRight N).map_spec p i j₁ (op V.left) _ n).trans ?_
      refine congrArg (fun z => (isTensorProductDgTensorRight P' N).tmul i j₁ (op V.left) z n) ?_
      exact (homSections_naturality (p.toHomologicalComplex.f i) V.hom.op x).symm
    have hmap := IsTensorProduct.map_assocTmul (isTensorProductDgTensorRight P N)
      (isTensorProductDgTensorRight N.toRightModule L)
      (isTensorProductDgTensorRight (dgTensorRight P N) L)
      (isTensorProductDgTensorRight P' N) (isTensorProductDgTensorRight (dgTensorRight P' N) L)
      ((dgTensorRightFunctor N ⋙ dgTensorRightFunctor L).map p) x
      ((p.toHomologicalComplex.f i).val.app (op U) x) hG j t
    refine (congrArg (fun z => ((dgTensorAssocIso N L P').hom.toHomologicalComplex.f
      (i + j)).val.app (op U) z) hmap).trans ?_
    refine (IsTensorProduct.uniqueIso_hom_tmul _ _ i j (op U) _ t).trans ?_
    refine ((tensorFunctorDataDgTensorRight (bimoduleTensor N L)).map_spec p i j (op U) x
      t).symm.trans ?_
    exact congrArg (fun z => (((dgTensorRightFunctor (bimoduleTensor N L)).map
      p).toHomologicalComplex.f (i + j)).val.app (op U) z)
      (IsTensorProduct.uniqueIso_hom_tmul _ _ i j (op U) x t).symm

end RelativeTensor

end Functor

end SheafOfModules

end
