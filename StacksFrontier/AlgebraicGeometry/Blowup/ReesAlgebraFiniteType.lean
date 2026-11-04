module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraModule
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksCore.Tactic.StacksAttribute

/-!
# The graded module of ideal-power multiples is of finite type

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals and `F` a sheaf of
`𝒪_X`-modules of finite type. This file proves that the graded module
`⨁ₙ ℐⁿF = Stacks.Blowup.reesGradedModule ℐ F` over the Rees algebra `⨁ₙ ℐⁿ` is of finite type
in the sense of `SheafOfModules.GradedModule.IsFiniteType`.

## Main results

* `Stacks.Blowup.generatesDegreeZeroPiece_reesGradedModule`: a finite family of sections of `F`
  generating `F` over an open `U` generates the degree-zero piece of `⨁ₙ ℐⁿF` over `U`.
* `Stacks.Blowup.exists_sum_smulSection_reesGradedModule`: every homogeneous section of
  `⨁ₙ ℐⁿF` is, locally, a finite sum of products of sections of the degree-zero piece with
  homogeneous sections of the Rees algebra.
* `Stacks.Blowup.generates_reesGradedModule`: generators of `F` over `U` are generators of
  `⨁ₙ ℐⁿF` as a graded `⨁ₙ ℐⁿ`-module over `U`.
* `Stacks.Blowup.isFiniteType_reesGradedModule`: `⨁ₙ ℐⁿF` is of finite type as soon as `F` is.

## References

* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Blowup

universe u

attribute [local instance] Stacks.Algebraization.sectionsModuleΓSheaf

variable {X : Scheme.{u}} (I : X.IdealSheafData) (F : SheafOfModules.{u} X.ringCatSheaf)

/-! ### The degree-zero piece -/

/-- Every section of `F` is a section of the degree-zero piece `ℐ⁰F` of `⨁ₙ ℐⁿF`. -/
public lemma mem_reesMultiple_zero {U : (Opens X)ᵒᵖ} (x : F.val.obj U) :
    x ∈ (reesMultiple I 0 F).toSubmodule.obj U := by
  have h := smul_mem_reesMultiple I 0 F U.unop ((reesUnit I).eval U) x
  have he : reesPieceAmbient I 0 U.unop ((reesUnit I).eval U) • x = x :=
    (congrArg (fun a : Γ(X, U.unop) => a • x) (reesUnit_ambient I U)).trans (one_smul _ x)
  exact Eq.mpr (congrArg (· ∈ (reesMultiple I 0 F).toSubmodule.obj U) he.symm) h

/-- A section of `F`, read as a section of the degree-zero piece of `⨁ₙ ℐⁿF`. -/
public def reesSectionZero {U : (Opens X)ᵒᵖ} (x : F.val.obj U) :
    ((reesGradedModule I F).piece 0).val.obj U :=
  ⟨x, mem_reesMultiple_zero I F x⟩

/-- The underlying section of `F` of `reesSectionZero I F x` is `x`. -/
@[simp] public lemma reesSectionZero_val {U : (Opens X)ᵒᵖ} (x : F.val.obj U) :
    (reesSectionZero I F x).1 = x := rfl

/-! ### Transport along an equality of degrees -/

/-- Transporting a section of `⨁ₙ ℐⁿF` along an equality of degrees does not change the
underlying section of `F`. -/
public lemma val_castHom_reesGradedModule {i j : ℤ} (h : i = j) (U : (Opens X)ᵒᵖ)
    (z : ((reesGradedModule I F).piece i).val.obj U) :
    (SheafOfModules.castHom (reesGradedModule I F).piece h U z).1 = z.1 := by
  subst h; rfl

/-- Transporting a homogeneous section of the Rees algebra along an equality of degrees does not
change its image in `Γ(X, U)`. -/
public lemma reesPieceAmbient_castHom {i j : ℤ} (h : i = j) (U : X.Opens)
    (c : (reesPiece I i).val.obj (op U)) :
    reesPieceAmbient I j U (SheafOfModules.castHom (reesPiece I) h (op U) c) =
      reesPieceAmbient I i U c := by
  subst h; rfl

/-- The section of `F` underlying the action of a homogeneous section of the Rees algebra in a
fixed total degree: multiplication by its image in `Γ(X, U)`. -/
public lemma val_smulSection_reesGradedModule (k : ℤ) {d : ℤ} {U : (Opens X)ᵒᵖ}
    (x : ((reesGradedModule I F).piece d).val.obj U)
    (y : (reesPiece I (k - d)).val.obj U) :
    ((reesGradedModule I F).smulSection k x y).1 =
      reesPieceAmbient I (k - d) U.unop y • x.1 :=
  val_castHom_reesGradedModule I F (show d + (k - d) = k by omega) U
    ((reesGradedModule I F).smul d (k - d) U x y)

/-! ### Generation of the degree-zero piece -/

/-- A finite family of sections of `F` generating `F` over `U` generates the degree-zero piece of
`⨁ₙ ℐⁿF` over `U`. -/
public lemma generatesDegreeZeroPiece_reesGradedModule {U : X.Opens} {n : ℕ}
    (s : Fin n → F.val.obj (op U))
    (hs : PresheafOfModules.Generates (Opens.grothendieckTopology X) F.val s) :
    (reesGradedModule I F).GeneratesDegreeZeroPiece (fun i => reesSectionZero I F (s i)) := by
  intro V f y
  obtain ⟨S, hS, hcomb⟩ := hs V f y.1
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨c, hc⟩ := hcomb W g hg
  refine ⟨c, Subtype.ext ?_⟩
  refine Eq.trans ?_ hc
  refine (AddSubmonoidClass.coe_finsetSum _ _).trans (Finset.sum_congr rfl fun i _ => rfl)

/-! ### Generation in degree zero -/

/-- The sieve of opens on which a given section of `F` lies in the submodule spanned by the
products of homogeneous sections of `ℐᵏ` with sections of `F`. -/
public def reesSpanSieve (k : ℤ) {V : X.Opens} (x : F.val.obj (op V)) : Sieve V where
  arrows W g := Stacks.restr F.val g.op x ∈ reesMultipleSpan I k F W
  downward_closed := by
    intro W W' g hg h
    have hstep := restr_mem_reesMultipleSpan I k F (leOfHom h) hg
    rw [show (homOfLE (leOfHom h)) = h from Subsingleton.elim _ _] at hstep
    exact (SheafOfModules.restr_comp F.val g.op h.op x) ▸ hstep

/-- The sieve on which a homogeneous section of `ℐᵏF` lies in the span of the products is
covering. -/
public lemma reesSpanSieve_mem (k : ℤ) {V : X.Opens}
    (x : ((reesGradedModule I F).piece k).val.obj (op V)) :
    reesSpanSieve I F k x.1 ∈ Opens.grothendieckTopology X V := by
  rw [Opens.mem_grothendieckTopology]
  intro pt hpt
  obtain ⟨W, hW, hptW, hspan⟩ := x.2 pt hpt
  exact ⟨W, homOfLE hW, hspan, hptW⟩

/-- `⨁ₙ ℐⁿF` is generated in degree zero: every homogeneous section of `⨁ₙ ℐⁿF` is, locally, a
finite sum of products of sections of the degree-zero piece with homogeneous sections of the Rees
algebra. -/
public lemma exists_sum_smulSection_reesGradedModule (k : ℤ) (V : X.Opens)
    (x : ((reesGradedModule I F).piece k).val.obj (op V)) :
    ∃ S : Sieve V, S ∈ Opens.grothendieckTopology X V ∧
      ∀ (W : X.Opens) (g : W ⟶ V), S g →
        ∃ (q : ℕ) (y : Fin q → ((reesGradedModule I F).piece 0).val.obj (op W))
          (b : Fin q → ((reesGradedAlgebra I).piece (k - 0)).val.obj (op W)),
          ∑ j, (reesGradedModule I F).smulSection k (y j) (b j) =
            ((reesGradedModule I F).piece k).val.restrictₛₗ g.op x := by
  refine ⟨reesSpanSieve I F k x.1, reesSpanSieve_mem I F k x, fun W g hg => ?_⟩
  obtain ⟨q, c, gen, hsum⟩ := Submodule.mem_span_set'.1 hg
  choose r m hrm using fun j => (gen j).2
  refine ⟨q, fun j => reesSectionZero I F (m j),
    fun j => SheafOfModules.castHom (reesPiece I) (show k = k - 0 by omega) (op W)
      (c j • r j), Subtype.ext ?_⟩
  refine ((AddSubmonoidClass.coe_finsetSum _ _).trans
    (Finset.sum_congr rfl fun j _ => ?_)).trans hsum
  rw [val_smulSection_reesGradedModule, reesPieceAmbient_castHom, reesPieceAmbient_smul,
    reesSectionZero_val, hrm j]
  exact (smul_smul (show Γ(X, W) from c j) (reesPieceAmbient I k W (r j)) (m j)).symm

/-! ### Finite type -/

/-- Generators of `F` over an open `U` are generators of `⨁ₙ ℐⁿF` as a graded `⨁ₙ ℐⁿ`-module
over `U`, all in degree zero. -/
public lemma generates_reesGradedModule {U : X.Opens} {n : ℕ} (s : Fin n → F.val.obj (op U))
    (hs : PresheafOfModules.Generates (Opens.grothendieckTopology X) F.val s) :
    (reesGradedModule I F).Generates (fun _ : Fin n => (0 : ℤ))
      (fun i => reesSectionZero I F (s i)) :=
  SheafOfModules.GradedModule.generates_of_degreeZero _ _
    (generatesDegreeZeroPiece_reesGradedModule I F s hs)
    (exists_sum_smulSection_reesGradedModule I F)

/-- The graded module `⨁ₙ ℐⁿF` over the Rees algebra `⨁ₙ ℐⁿ` is of finite type as soon as `F`
is of finite type over `𝒪_X`. -/
public theorem isFiniteType_reesGradedModule
    [hF : PresheafOfModules.IsFiniteType (Opens.grothendieckTopology X) F.val] :
    (reesGradedModule I F).IsFiniteType where
  exists_generators := by
    obtain ⟨K, U, hU, hgen⟩ := hF.exists_generators
    refine ⟨K, U, hU, fun i => ?_⟩
    obtain ⟨n, s, hs⟩ := hgen i
    exact ⟨n, fun _ => 0, fun j => reesSectionZero I F (s j),
      generates_reesGradedModule I F s hs⟩

end Stacks.Blowup

end
