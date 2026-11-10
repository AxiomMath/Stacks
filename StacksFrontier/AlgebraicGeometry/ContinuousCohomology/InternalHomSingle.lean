module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomComplex
public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# The internal Hom complex into a single module

Let `E` be a cochain complex of discrete `R`-`Q`-modules and `W` a discrete `ℤ`-`Q`-module placed
in degree `q`. The internal Hom complex `Hom^•_ℤ(E, W[-q])` has `Hom_ℤ(E^{q-n}, W)` in degree `n`.
So does the complex obtained by applying the contravariant internal Hom `Hom_ℤ(-, W)` to `E` read
backwards (`CochainComplex.opEquivalence`) and shifting by `-q`. The two differentials differ by
the sign `(-1)^{n+1+q}`, and the degreewise identifications twisted by
`ε(n) = (-1)^{n(n+1)/2 + q n}` form an isomorphism of complexes of `Rᵐᵒᵖ[[Q]]`-modules.

For `W = ℚ/ℤ` this identifies the internal Hom complex into `ℚ/ℤ[-q]` with the contragredient
complex of `E`, shifted by `-q`, which computes the derived contragredient.

## Main definitions

* `Stacks.ContinuousCohomology.internalHomSingleIso`: the isomorphism of complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex Stacks.GroupHomology Opposite

universe u v w

namespace Stacks.ContinuousCohomology

/-- The sign `ε(n) = (-1)^{n(n+1)/2 + q n}`. -/
def singleSign (q n : ℤ) : ℤˣ := (n * (n + 1) / 2 + q * n).negOnePow

/-- The recursion `ε(n + 1) = ε(n) (-1)^{n+1+q}`. -/
lemma singleSign_succ (q n : ℤ) :
    singleSign q (n + 1) = singleSign q n * (n + 1 + q).negOnePow := by
  unfold singleSign
  rw [← Int.negOnePow_add]
  congr 1
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

variable (R : Type u) [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q]
  (E : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ)
  (W : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) (q : ℤ)

/-- The contravariant internal Hom `Hom_ℤ(-, W)` is additive. -/
instance internalHom_flip_obj_additive : ((internalHom.{u, v, w, w} R Q).flip.obj W).Additive where
  map_add {X _ f g} :=
    ModuleCat.hom_ext <| LinearMap.ext fun (χ : X.unop.obj.obj.V →+ W.obj.obj.V) ↦
      AddMonoidHom.ext fun v ↦ map_add χ (f.unop.hom.hom.hom.hom v) (g.unop.hom.hom.hom.hom v)

/-- The complex `Hom_ℤ(-, W)` applied to `E` read backwards: degree `m` is `Hom_ℤ(E^{-m}, W)`. -/
abbrev internalHomOpComplex :
    CochainComplex (ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q)) ℤ :=
  (((internalHom.{u, v, w, w} R Q).flip.obj W).mapHomologicalComplex _).obj
    ((CochainComplex.opEquivalence _).functor.obj (op E))

/-- The single complex `W[-q]`, with `W` in degree `q`. -/
abbrev singleComplex : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ :=
  (CochainComplex.singleFunctor _ q).obj W

/-- The projection of the degree-`q` term of `W[-q]` to `W`, on underlying abelian groups. -/
abbrev singleProj : (forgetAb ℤ Q).obj ((singleComplex W q).X q) ⟶ (forgetAb ℤ Q).obj W :=
  (forgetAb ℤ Q).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q W).hom

open InternalHomCochain

omit [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The underlying complex of abelian groups of `W[-q]` vanishes outside degree `q`. -/
lemma isZero_underlyingAb_singleComplex_X (q' : ℤ) (h : q' ≠ q) :
    IsZero ((underlyingAb ℤ (singleComplex W q)).X q') :=
  (forgetAb ℤ Q).map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

/-- The inverse of `singleProj`. -/
abbrev singleIncl : (forgetAb ℤ Q).obj W ⟶ (forgetAb ℤ Q).obj ((singleComplex W q).X q) :=
  (forgetAb ℤ Q).map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q W).inv

omit [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `singleIncl` followed by `singleProj` is the identity. -/
@[reassoc (attr := simp)]
lemma singleIncl_singleProj : singleIncl W q ≫ singleProj W q = 𝟙 _ := by
  rw [← Functor.map_comp, Iso.inv_hom_id]
  exact (forgetAb ℤ Q).map_id _

omit [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `singleProj` followed by `singleIncl` is the identity. -/
@[reassoc (attr := simp)]
lemma singleProj_singleIncl : singleProj W q ≫ singleIncl W q = 𝟙 _ := by
  rw [← Functor.map_comp, Iso.hom_inv_id]
  exact (forgetAb ℤ Q).map_id _

/-- The degree-`n` component: a cochain `z` goes to `ε(n)` times its component
`E^{q-n} → W`. -/
def internalHomSingleFun (n : ℤ) (z : InternalHomCochain R E (singleComplex W q) n) :
    (forgetAb R Q).obj (E.X (-(n + -q))) ⟶ (forgetAb ℤ Q).obj W :=
  singleSign q n • ((toCochain z).v (-(n + -q)) q (by omega) ≫ singleProj W q)

/-- The inverse of the degree-`n` component. -/
def internalHomSingleInv (n : ℤ) (f : (forgetAb R Q).obj (E.X (-(n + -q))) ⟶ (forgetAb ℤ Q).obj W) :
    InternalHomCochain R E (singleComplex W q) n :=
  of (singleSign q n • Cochain.single
    (K := underlyingAb R E) (L := underlyingAb ℤ (singleComplex W q)) (f ≫ singleIncl W q) n)

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `internalHomSingleInv` is a right inverse of `internalHomSingleFun`. -/
lemma internalHomSingleFun_inv (n : ℤ)
    (f : (forgetAb R Q).obj (E.X (-(n + -q))) ⟶ (forgetAb ℤ Q).obj W) :
    internalHomSingleFun R E W q n (internalHomSingleInv R E W q n f) = f := by
  unfold internalHomSingleFun internalHomSingleInv
  rw [toCochain_of, Cochain.units_smul_v, Cochain.single_v, Linear.units_smul_comp,
    Category.assoc, singleIncl_singleProj, Category.comp_id, smul_smul, Int.units_mul_self,
    one_smul]

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- `internalHomSingleInv` is a left inverse of `internalHomSingleFun`. -/
lemma internalHomSingleInv_fun (n : ℤ) (z : InternalHomCochain R E (singleComplex W q) n) :
    internalHomSingleInv R E W q n (internalHomSingleFun R E W q n z) = z := by
  apply InternalHomCochain.ext
  refine Cochain.ext _ _ fun p' q' hpq' => ?_
  unfold internalHomSingleFun internalHomSingleInv
  rw [toCochain_of, Cochain.units_smul_v]
  by_cases hq' : q' = q
  · subst hq'
    obtain rfl : p' = -(n + -q') := by omega
    rw [Cochain.single_v, Linear.units_smul_comp, smul_smul,
      Int.units_mul_self, one_smul, Category.assoc, singleProj_singleIncl]
    exact Category.comp_id _
  · exact (isZero_underlyingAb_singleComplex_X W q q' hq').eq_of_tgt _ _

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The degree-`n` component is additive. -/
lemma internalHomSingleFun_add (n : ℤ) (z z' : InternalHomCochain R E (singleComplex W q) n) :
    internalHomSingleFun R E W q n (z + z') =
      internalHomSingleFun R E W q n z + internalHomSingleFun R E W q n z' := by
  unfold internalHomSingleFun
  rw [toCochain_add, Cochain.add_v, Preadditive.add_comp, smul_add]

/-- The degree-`n` component commutes with the action of `Rᵐᵒᵖ[[Q]]`. -/
lemma internalHomSingleFun_smul (n : ℤ) (x : CompletedGroupAlgebra Rᵐᵒᵖ Q)
    (z : InternalHomCochain R E (singleComplex W q) n) :
    internalHomSingleFun R E W q n (x • z) =
      compSMul R x (internalHomSingleFun R E W q n z) := by
  unfold internalHomSingleFun
  rw [toCochain_smul_v, compSMul_comp R (HomologicalComplex.singleObjXSelf _ q W).hom,
    compSMul_units_smul]

omit [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The differentials of the underlying complex of abelian groups of `W[-q]` vanish. -/
lemma underlyingAb_singleComplex_d (i j : ℤ) :
    (underlyingAb ℤ (singleComplex W q)).d i j = 0 := by
  change (forgetAb ℤ Q).map ((singleComplex W q).d i j) = 0
  rw [CochainComplex.singleFunctor_obj_d, Functor.map_zero]

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- **The components commute with the differentials**, up to the sign `(-1)^q` of the shift:
`φ_{n+1}(δ z) = (-1)^q (d_E ≫ φ_n(z))`. -/
lemma internalHomSingleFun_δ (n : ℤ) (z : InternalHomCochain R E (singleComplex W q) n) :
    internalHomSingleFun R E W q (n + 1) (of (δ n (n + 1) (toCochain z))) =
      (-q).negOnePow • ((forgetAb R Q).map (E.d (-(n + 1 + -q)) (-(n + -q))) ≫
        internalHomSingleFun R E W q n z) := by
  have hsign : singleSign q (n + 1) * (n + 1).negOnePow = (-q).negOnePow * singleSign q n := by
    rw [singleSign_succ, Int.negOnePow_neg, mul_assoc, ← Int.negOnePow_add,
      show n + 1 + q + (n + 1) = q + 2 * (n + 1) by ring, Int.negOnePow_add,
      Int.negOnePow_two_mul, mul_one, mul_comm]
  unfold internalHomSingleFun
  rw [toCochain_of, δ_v n (n + 1) rfl _ (-(n + 1 + -q)) q (by omega) (q - 1) (-(n + -q))
    (by omega) (by omega), underlyingAb_singleComplex_d, Limits.comp_zero, zero_add]
  simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
    smul_smul]
  congr 1
  exact_mod_cast congrArg (fun u : ℤˣ => (u : ℤ)) hsign

/-- **The degree-`n` identification** `Hom^n_ℤ(E, W[-q]) ≃ Hom_ℤ(E^{q-n}, W)`, twisted by `ε(n)`,
as an `Rᵐᵒᵖ[[Q]]`-linear equivalence onto the degree-`n` term of the shifted contravariant
complex. -/
def internalHomSingleLinearEquiv (n : ℤ) :
    (internalHomComplex R E (singleComplex W q)).X n ≃ₗ[CompletedGroupAlgebra Rᵐᵒᵖ Q]
      ((internalHomOpComplex R E W)⟦-q⟧).X n where
  toFun z := (internalHomSingleFun R E W q n z).hom
  invFun φ := internalHomSingleInv R E W q n (AddCommGrpCat.ofHom φ)
  left_inv z := internalHomSingleInv_fun R E W q n z
  right_inv φ := congrArg AddCommGrpCat.Hom.hom
    (internalHomSingleFun_inv R E W q n (AddCommGrpCat.ofHom φ))
  map_add' z z' := congrArg AddCommGrpCat.Hom.hom (internalHomSingleFun_add R E W q n z z')
  map_smul' x z := congrArg AddCommGrpCat.Hom.hom (internalHomSingleFun_smul R E W q n x z)

/-- **The internal Hom complex into `W[-q]` is the contravariant complex `Hom_ℤ(E, W)`,
shifted by `-q`**, with the degreewise sign `ε(n) = (-1)^{n(n+1)/2 + q n}`. -/
def internalHomSingleIso :
    internalHomComplex R E (singleComplex W q) ≅ (internalHomOpComplex R E W)⟦-q⟧ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (internalHomSingleLinearEquiv R E W q n).toModuleIso) (by
      rintro n _ rfl
      refine ModuleCat.hom_ext <| LinearMap.ext fun z => AddMonoidHom.ext fun v => ?_
      change _ = (internalHomSingleFun R E W q (n + 1) (of (δ n (n + 1) (toCochain z)))).hom v
      refine Eq.trans ?_
        (congrArg (fun f => AddCommGrpCat.Hom.hom f v) (internalHomSingleFun_δ R E W q n z)).symm
      simp [CochainComplex.shiftFunctor_obj_d', Units.smul_def, internalHomSingleLinearEquiv]
      rfl)

end Stacks.ContinuousCohomology

end
