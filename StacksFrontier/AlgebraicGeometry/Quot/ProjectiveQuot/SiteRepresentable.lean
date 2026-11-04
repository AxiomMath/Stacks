module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction

/-!
# A presheaf on schemes represented by a proper scheme, on the big fppf site over `Spec ℤ`

Stacks 0DPA asserts that the Quot functor `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}` is represented by a scheme
proper over `Spec ℤ`, while its consequences are statements about algebraic spaces on the big
fppf site over `Spec ℤ`.  This file transports the first kind of statement to the second.

A scheme `X` proper over `Spec ℤ` is of finite type and quasi-compact over the base
`AlgebraicGeometry.integerBase`, so it is an object of every big fppf site; as an object of the
site over `Spec ℤ` (`AlgebraicGeometry.CurveFamily.ofScheme`) its morphisms from an object `T`
are exactly the morphisms of schemes from the underlying scheme of `T` to `X`, every morphism of
schemes commuting with the structure morphisms to the terminal scheme `Spec ℤ`.  Hence the
restriction to the site of a presheaf on schemes represented by `X` is represented on the site
by this object, which is an algebraic space (Stacks 025Z) proper over the base.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.yonedaOfSchemeIso`: the presheaf represented on the site by
  a scheme of the site is the restriction of the presheaf represented by it on schemes.
* `AlgebraicGeometry.ProjectiveQuot.exists_model_isAlgebraicSpace_isProper_of_iso`: a presheaf
  on the site which is the restriction of a presheaf on schemes represented by a scheme proper
  over `Spec ℤ` has a small model which is an algebraic space proper over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuot

universe u

/-- Every morphism of schemes from a scheme proper over the terminal scheme to `Spec ℤ` is
proper: it is the morphism to the terminal scheme followed by the isomorphism of the terminal
scheme with `Spec ℤ`. -/
theorem isProper_of_isProper_terminal_from {X : Scheme.{u}} (hX : IsProper (terminal.from X))
    (g : X ⟶ integerBase.{u}) : IsProper g := by
  let e : (⊤_ Scheme.{u}) ≅ integerBase.{u} :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  obtain rfl : terminal.from X ≫ e.hom = g := specULiftZIsTerminal.hom_ext _ _
  exact MorphismProperty.comp_mem @IsProper (terminal.from X) e.hom hX inferInstance

/-- A scheme proper over the terminal scheme is contained in every big fppf site: it is of
finite type and quasi-compact over `Spec ℤ`, which the site contains. -/
theorem contains_of_isProper_terminal_from (B : BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : IsProper (terminal.from X)) : B.Contains X := by
  let ν : X ⟶ (BigFppfOver.toScheme B integerBase B.contains_integerBase).obj (siteBase B) :=
    specULiftZIsTerminal.from X
  have := isProper_of_isProper_terminal_from hX ν
  exact Space.contains_of_locallyOfFiniteType_of_quasiCompact B integerBase
    B.contains_integerBase ν

/-- The morphisms in the big fppf site over `Spec ℤ` from an object `T` to a scheme `X` of the
site are the morphisms of schemes from the underlying scheme of `T` to `X`. -/
def homOfSchemeEquiv {B : BigFppfSite.{u}} {X : Scheme.{u}} (hX : B.Contains X)
    (T : BigFppfOver B integerBase B.contains_integerBase) :
    (T ⟶ CurveFamily.ofScheme X hX) ≃
      ((BigFppfOver.toScheme B integerBase B.contains_integerBase).obj T ⟶ X) where
  toFun f := (BigFppfOver.toScheme B integerBase B.contains_integerBase).map f
  invFun g := CurveFamily.homOfScheme g
  left_inv _ := (BigFppfOver.toScheme B integerBase B.contains_integerBase).map_injective rfl
  right_inv _ := rfl

/-- The presheaf represented on the big fppf site over `Spec ℤ` by a scheme `X` of the site is
the restriction to the site of the presheaf represented by `X` on all schemes. -/
def yonedaOfSchemeIso {B : BigFppfSite.{u}} {X : Scheme.{u}} (hX : B.Contains X) :
    yoneda.obj (CurveFamily.ofScheme (hZ := B.contains_integerBase) X hX) ≅
      (BigFppfOver.toScheme B integerBase B.contains_integerBase).op ⋙ yoneda.obj X :=
  NatIso.ofComponents (fun T ↦ (homOfSchemeEquiv hX T.unop).toIso) fun f ↦ by
    ext x
    exact (BigFppfOver.toScheme B integerBase B.contains_integerBase).map_comp f.unop x

/-- **Representability on the site by a proper scheme.** Let `Q` be a presheaf on the big fppf
site over `Spec ℤ` which is the restriction of a presheaf `F` on all schemes, and suppose `F` is
represented by a scheme `X` proper over the terminal scheme `Spec ℤ`.  Then `Q` has a small model
`M`, an algebraic space over `Spec ℤ` whose morphism to the base is proper; `M` is the presheaf
represented on the site by `X` itself. -/
theorem exists_model_isAlgebraicSpace_isProper_of_iso (B : BigFppfSite.{u})
    (Q : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ ⥤ Type (u + 1))
    (F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1))
    (e : Q ≅ (BigFppfOver.toScheme B integerBase B.contains_integerBase).op ⋙ F)
    (hrep : ∃ X : Scheme.{u}, IsProper (terminal.from X) ∧
      Nonempty (F ≅ yoneda.obj X ⋙ uliftFunctor.{u + 1})) :
    ∃ (M : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ ⥤ Type u)
      (_ : M ⋙ uliftFunctor.{u + 1} ≅ Q),
      IsAlgebraicSpace B integerBase B.contains_integerBase M ∧
        ∀ b : M ⟶ yoneda.obj (siteBase B),
          Space.IsProper B integerBase B.contains_integerBase b := by
  obtain ⟨X, hX, ⟨hF⟩⟩ := hrep
  have hXB : B.Contains X := contains_of_isProper_terminal_from B hX
  let Xsite : BigFppfOver B integerBase B.contains_integerBase := CurveFamily.ofScheme X hXB
  refine ⟨yoneda.obj Xsite,
    Functor.isoWhiskerRight (yonedaOfSchemeIso hXB) uliftFunctor.{u + 1} ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (BigFppfOver.toScheme B integerBase B.contains_integerBase).op
        hF.symm ≪≫ e.symm,
    isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Xsite, fun b ↦ ?_⟩
  rw [Subsingleton.elim b (yoneda.map ((isTerminal_siteBase B).from Xsite))]
  exact (Space.isProper_yoneda_map_iff B integerBase B.contains_integerBase _).2
    (isProper_of_isProper_terminal_from hX _)

end AlgebraicGeometry.ProjectiveQuot

end
