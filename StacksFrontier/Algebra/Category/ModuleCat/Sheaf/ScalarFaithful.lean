module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeOfIntRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphisms
public import StacksFrontier.CategoryTheory.Preadditive.MatrixKernelSplitting

/-!
# Sheaves of modules on which the structure sheaf acts faithfully

A sheaf of modules `M` over a sheaf of rings `R` on a site is *scalar faithful* when the action
map `R ⟶ ℋom_R(M, M)` is injective: a section `s` of `R` over `U` which kills every section of
`M` over every object over `U` is zero. A finite locally free module of rank one is scalar
faithful. On a site with a terminal object, a scalar faithful kernel of a matrix `A` over the
global sections admits no nonzero `x` with `N A = x · 1`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.IsScalarFaithful`.

## Main results

* `AlgebraicGeometry.SheafOfModules.isScalarFaithful_of_isFiniteLocallyFreeOfIntRank_one`.
* `AlgebraicGeometry.SheafOfModules.IsScalarFaithful.of_iso`.
* `AlgebraicGeometry.SheafOfModules.IsScalarFaithful.eq_zero_of_mul_eq_smul_one`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ u₁

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **The action `R ⟶ ℋom_R(M, M)` is injective.** On sections over `U`, the image of `s` is the
endomorphism of `M|_U` given by multiplication by `s`; it is zero exactly when the restriction of
`s` kills every section of `M` over every object mapping to `U`. -/
def IsScalarFaithful (M : _root_.SheafOfModules.{u} R) : Prop :=
  ∀ (U : Cᵒᵖ) (s : R.obj.obj U),
    (∀ (V : Cᵒᵖ) (i : U ⟶ V) (m : M.val.obj V), (R.obj.map i).hom s • m = 0) → s = 0

/-- Scalar faithfulness is invariant under isomorphism. -/
theorem IsScalarFaithful.of_iso {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N)
    (hM : IsScalarFaithful M) : IsScalarFaithful N := by
  intro U s hs
  refine hM U s fun V i m => ?_
  have h := hs V i ((e.hom.val.app V) m)
  rw [← (e.hom.val.app V).hom.map_smul] at h
  have h' := congrArg (e.inv.val.app V).hom h
  rw [map_zero] at h'
  refine Eq.trans ?_ h'
  show _ = ((e.hom ≫ e.inv).val.app V).hom _
  rw [e.hom_inv_id]
  rfl

section Terminal

variable {O : Sheaf J CommRingCat.{u}} [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {T : C} (hT : IsTerminal T)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
open Stacks.SheafOfModules in
/-- **A scalar faithful kernel of a matrix admits no left inverse up to a nonzero scalar.** On a
site with a terminal object `T`, let `A` be a matrix over `O(T)`. If the kernel of `A : O^n ⟶ O^m`
is scalar faithful and `N A = x · 1`, then `x = 0`: multiplication by `x` is zero on the kernel. -/
theorem IsScalarFaithful.eq_zero_of_mul_eq_smul_one {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) (O.obj.obj (op T))}
    (hK : IsScalarFaithful (kernel (matrixHomMatrixKernelSplitting
      (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O)))
      (unitEndRingHom O hT) A)))
    {N : Matrix (Fin n) (Fin m) (O.obj.obj (op T))} {x : O.obj.obj (op T)}
    (hN : N * A = x • (1 : Matrix (Fin n) (Fin n) (O.obj.obj (op T)))) : x = 0 := by
  have : ∀ U, IsMulCommutative (((Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj U) := fun U =>
    ⟨⟨fun a b => mul_comm (G := O.obj.obj U) a b⟩⟩
  let μ := terminalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf O)) T hT x
  have hunit : μ.app (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O))) =
      unitEndRingHom O hT x := by
    apply (unitEndRingEquiv O hT).injective
    show _ = (unitEndRingEquiv O hT) ((unitEndRingEquiv O hT).symm x)
    rw [RingEquiv.apply_symm_apply]
    show ((Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.map (hT.from T).op x * 1 = x
    rw [mul_one, show hT.from T = 𝟙 T from hT.hom_ext _ _, op_id, CategoryTheory.Functor.map_id]
    rfl
  have hK0 := app_kernel_matrixHom_eq_zero_matrixKernelSplitting μ hunit hN
  refine hK (op T) x fun V i k => ?_
  obtain rfl : i = (hT.from V.unop).op := Quiver.Hom.unop_inj (hT.hom_ext _ _)
  have := congrArg (fun φ => φ.val.app V k) hK0
  exact this

end Terminal

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A finite locally free module of rank one is scalar faithful.** Locally it has a basis
element `e`, and `t • e = 0` forces `t = 0`; the structure sheaf is separated. -/
theorem isScalarFaithful_of_isFiniteLocallyFreeOfIntRank_one (M : _root_.SheafOfModules.{u} R)
    (h : IsFiniteLocallyFreeOfIntRank M 1) : IsScalarFaithful M := by
  obtain ⟨q, hq, hrank⟩ := h
  intro U s hs
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (M := _root_.SheafOfModules.unit R) s
    (q.coversTop U.unop) fun V g hg => ?_
  obtain ⟨i, ⟨f⟩⟩ := hg
  obtain ⟨n, hn, ⟨ε⟩⟩ := hrank i
  obtain rfl : n = 1 := by exact_mod_cast hn
  let σ := q.generators i
  let j₀ : σ.I := ε.symm 0
  have : IsIso σ.π := hq.isIso i
  let ρ : _root_.SheafOfModules.free σ.I ⟶ _root_.SheafOfModules.unit (R.over (q.X i)) :=
    (_root_.SheafOfModules.unit (R.over (q.X i))).freeHomEquiv.symm
      (fun _ => (_root_.SheafOfModules.unit (R.over (q.X i))).unitHomEquiv (𝟙 _))
  let φ := inv σ.π ≫ ρ
  let W : (Over (q.X i))ᵒᵖ := op (Over.mk f)
  let m : (M.over (q.X i)).val.obj W := (σ.s j₀).val W
  have key {N : _root_.SheafOfModules.{u} (R.over (q.X i))} (f : σ.I → N.sections) :
      ((N.freeHomEquiv.symm f).val.app W) ((_root_.SheafOfModules.freeSection j₀).val W) =
        (f j₀).val W :=
    congrArg (fun t => t.val W)
      (_root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection f j₀)
  have hφm : φ.val.app W m = (1 : (R.over (q.X i)).obj.obj W) := by
    refine (congrArg (φ.val.app W) (key σ.s).symm).trans ?_
    show (σ.π ≫ inv σ.π ≫ ρ).val.app W _ = _
    rw [IsIso.hom_inv_id_assoc]
    exact key _
  let t : (R.over (q.X i)).obj.obj W := (R.obj.map g.op).hom s
  have h0 : t • m = 0 := hs (op V) g.op (show M.val.obj (op V) from m)
  have h1 := congrArg (φ.val.app W) h0
  rw [map_zero, (φ.val.app W).hom.map_smul, hφm] at h1
  exact (mul_one t).symm.trans h1

end AlgebraicGeometry.SheafOfModules
