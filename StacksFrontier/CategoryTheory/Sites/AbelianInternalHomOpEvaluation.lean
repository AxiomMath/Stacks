module

public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpComplex

/-!
# Evaluation on the internal Hom complex

For a complex `L` of sheaves of `Λ`-modules and a complex `M` of abelian sheaves on a site, a
section `e` of `ℋom^p_ℤ(L, M)` over `U` has a component `e_n : L^n|_U ⟶ M^q|_U` for every
`p + n = q`, and evaluating it at the identity of `U` on a section `a` of `L^n` over `U` gives
the section `ev(a, e) = e_n(a)` of `M^q` over `U`
(`Stacks.AbelianInternalHom.homOpEval`). This pairing is natural in `U`
(`Stacks.AbelianInternalHom.homOpEval_naturality`), satisfies the Leibniz rule of the
Hom-complex differential `ev(a, δe) = d(ev(a, e)) + (-1)^{p+1} ev(d a, e)`
(`Stacks.AbelianInternalHom.homOpEval_d`), is balanced for the actions of `Λ` and `Λᵐᵒᵖ`
(`Stacks.AbelianInternalHom.homOpEval_smul`), and is compatible with precomposition
(`Stacks.AbelianInternalHom.homOpEval_precomp`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MulOpposite Stacks.ModuleCatLift

universe w v u

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {Λ : Type w} [Ring Λ]
  (L : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ)
  (M : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ)

/-- The component `e_n ∈ ℋom_ℤ(L^n, M^q)(U)` of a section `e` of `ℋom^p_ℤ(L, M)` over `U`, as a
morphism of abelian presheaves on the slice over `U`. -/
def homOpComponent (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ)
    (e : (homOpComplexX K L M p).obj.obj U) :
    (Over.forget U.unop).op ⋙ (toAb K (L.X n)).obj ⟶ (Over.forget U.unop).op ⋙ (M.X q).obj :=
  ((homOpComplexπ K L M p (⟨(n, q), by omega⟩ : HomOpIndex p)).hom.app U).hom e

/-- Evaluation `ev(a, e) = e_n(a)` of a section `e` of `ℋom^p_ℤ(L, M)` over `U` on a section
`a` of `L^n` over `U`, for `p + n = q`. -/
def homOpEval (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ) :
    (L.X n).obj.obj U →+ (homOpComplexX K L M p).obj.obj U →+ (M.X q).obj.obj U where
  toFun a :=
    { toFun e := ((homOpComponent K L M n p q h U e).app (op (Over.mk (𝟙 U.unop)))).hom a
      map_zero' := by
        unfold homOpComponent
        rw [map_zero]
        rfl
      map_add' e e' := by
        unfold homOpComponent
        rw [map_add]
        rfl }
  map_zero' := AddMonoidHom.ext fun e => by
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
    exact map_zero _
  map_add' a a' := AddMonoidHom.ext fun e => by
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
    exact map_add _ a a'

/-- `ev(a, e)` is the component `e_n` evaluated at the identity of `U` on `a`. -/
lemma homOpEval_apply (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ) (a : (L.X n).obj.obj U)
    (e : (homOpComplexX K L M p).obj.obj U) :
    homOpEval K L M n p q h U a e =
      ((homOpComponent K L M n p q h U e).app (op (Over.mk (𝟙 U.unop)))).hom a := by
  simp only [homOpEval, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- The component of a restricted section is the restricted component. -/
lemma homOpComponent_map (n p q : ℤ) (h : p + n = q) {U V : Cᵒᵖ} (f : U ⟶ V)
    (e : (homOpComplexX K L M p).obj.obj U) :
    homOpComponent K L M n p q h V (((homOpComplexX K L M p).obj.map f).hom e) =
      Functor.whiskerLeft (Over.map f.unop).op (homOpComponent K L M n p q h U e) := by
  have := ConcreteCategory.congr_hom
    ((homOpComplexπ K L M p (⟨(n, q), by omega⟩ : HomOpIndex p)).hom.naturality f) e
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this

/-- Evaluation commutes with restriction. -/
lemma homOpEval_naturality (n p q : ℤ) (h : p + n = q) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (L.X n).obj.obj U) (e : (homOpComplexX K L M p).obj.obj U) :
    ((M.X q).obj.map f).hom (homOpEval K L M n p q h U a e) =
      homOpEval K L M n p q h V (((L.X n).obj.map f).hom a)
        (((homOpComplexX K L M p).obj.map f).hom e) := by
  rw [homOpEval_apply, homOpEval_apply, homOpComponent_map, Functor.whiskerLeft_app]
  let φ : (Over.map f.unop).obj (Over.mk (𝟙 V.unop)) ⟶ Over.mk (𝟙 U.unop) :=
    Over.homMk f.unop (by simp)
  exact (ConcreteCategory.congr_hom ((homOpComponent K L M n p q h U e).naturality φ.op) a).symm

/-- The components of the differential of a section. -/
lemma homOpComponent_d (n p r : ℤ) (hr : p + 1 + n = r) (U : Cᵒᵖ)
    (e : (homOpComplexX K L M p).obj.obj U) :
    homOpComponent K L M n (p + 1) r hr U (((homOpComplexD K L M p).hom.app U).hom e) =
      homOpComponent K L M n p (r - 1) (by omega) U e ≫
          Functor.whiskerLeft (Over.forget U.unop).op (M.d (r - 1) r).hom +
        (p + 1).negOnePow • (Functor.whiskerLeft (Over.forget U.unop).op
          ((sheafCompose K (forget₂ (ModuleCat.{max u v} Λ) AddCommGrpCat.{max u v})).map
            (L.d n (n + 1))).hom ≫ homOpComponent K L M (n + 1) p r (by omega) U e) := by
  have h1 := congrArg (fun φ => (φ.hom.app U).hom e)
    (homOpComplexD_π K L M p (⟨(n, r), by simp only; omega⟩ : HomOpIndex (p + 1)))
  exact h1.trans (by unfold homOpComplexDComponent; rfl)

/-- The Leibniz rule for evaluation: `ev(a, δe) = d(ev(a, e)) + (-1)^{p+1} ev(d a, e)`. -/
lemma homOpEval_d (n p r : ℤ) (hr : p + 1 + n = r) (U : Cᵒᵖ) (a : (L.X n).obj.obj U)
    (e : (homOpComplexX K L M p).obj.obj U) :
    homOpEval K L M n (p + 1) r hr U a (((homOpComplexD K L M p).hom.app U).hom e) =
      ((M.d (r - 1) r).hom.app U).hom (homOpEval K L M n p (r - 1) (by omega) U a e) +
        (p + 1).negOnePow • homOpEval K L M (n + 1) p r (by omega) U
          (((L.d n (n + 1)).hom.app U).hom a) e := by
  rw [homOpEval_apply, homOpEval_apply, homOpEval_apply, homOpComponent_d]
  rfl

/-- Evaluation is balanced: `ev(λ a, e) = ev(a, op λ • e)`. -/
lemma homOpEval_smul (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ) (r : Λ) (a : (L.X n).obj.obj U)
    (e : (homOpComplexX K L M p).obj.obj U) :
    homOpEval K L M n p q h U (r • a) e = homOpEval K L M n p q h U a (MulOpposite.op r • e) := by
  rw [homOpEval_apply, homOpEval_apply]
  unfold homOpComponent
  rw [map_smul]
  rfl

/-- Evaluation is compatible with precomposition:
`ev(f a, e) = ev(a, f^* e)` for a morphism of complexes `f : L' ⟶ L`. -/
lemma homOpEval_precomp {L' : CochainComplex (Sheaf K (ModuleCat.{max u v} Λ)) ℤ} (f : L' ⟶ L)
    (n p q : ℤ) (h : p + n = q) (U : Cᵒᵖ) (a : (L'.X n).obj.obj U)
    (e : (homOpComplexX K L M p).obj.obj U) :
    homOpEval K L M n p q h U (((f.f n).hom.app U).hom a) e =
      homOpEval K L' M n p q h U a
        (((homOpComplexPrecompX (M := M) f p).hom.app U).hom e) := by
  rw [homOpEval_apply, homOpEval_apply]
  have h1 := congrArg (fun φ => (φ.hom.app U).hom e)
    (homOpComplexPrecompX_π K L M f p (⟨(n, q), by simp only; omega⟩ : HomOpIndex p))
  unfold homOpComponent
  change _ = ((((homOpComplexPrecompX (M := M) f p ≫ homOpComplexπ K L' M p
    (⟨(n, q), by simp only; omega⟩ : HomOpIndex p)).hom.app U).hom e).app
      (op (Over.mk (𝟙 U.unop)))).hom a
  rw [h1]
  rfl

end Stacks.AbelianInternalHom

end
