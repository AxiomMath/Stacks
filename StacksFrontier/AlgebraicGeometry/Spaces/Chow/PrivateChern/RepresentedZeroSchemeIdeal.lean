module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartIdealSheafAffineLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparisonIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpaceClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel

/-!
# The zero scheme of a section on a represented algebraic space

Let `T` be a scheme of the big fppf site, `h_T` the algebraic space it represents and `𝒩` an
invertible `𝒪_{h_T}`-module with a global section `τ`. The restriction `𝒩|_T` of `𝒩` to the
Zariski site of `T` (along the identity chart) is a module on the scheme `T`, and `τ` restricts to
a global section `τ|_T` of it. **The ideal sheaf of `T` cut out by the zero scheme `Z(τ) ⊆ h_T`
(Stacks 0845) is the zero scheme of `τ|_T` on the scheme `T`** (Stacks 01CY / 0B4A for schemes),
provided `𝒩|_T` is invertible: on an affine open `O ⊆ T` both are the ideal of `Γ(O, 𝒪)` generated
by the values of the linear functionals at the section, the sections of `𝒩` over the étale chart
`O ⟶ h_T` being the sections of `𝒩|_T` over `O`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.schemeSpaceIdeal_zeroScheme`: the comparison.

## References

* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- The restriction of an `𝒪_{h_T}`-module to the Zariski site of the scheme `T`. -/
abbrev representedRestriction
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    ((BigFppfOver.toScheme B S hS).obj T).Modules :=
  restrictToChartScheme B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) N
    (selfChart B S hS T)

/-- The restriction of a global section of an `𝒪_{h_T}`-module to the scheme `T`. -/
abbrev representedRestrictionSection
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (τ : N.sections) : Γ(representedRestriction B S hS T N, ⊤) :=
  chartSectionsToRestrict (schemeSpace T) N (selfChart B S hS T) ⊤
    (τ.eval (op (openChart B S hS (yoneda.obj T) (selfChart B S hS T) ⊤)))

/-- **The zero scheme of a section of an invertible module on a represented algebraic space,
read on the representing scheme.** -/
theorem schemeSpaceIdeal_zeroScheme
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (schemeSpace T))
      (structureRingSheaf B S hS (schemeSpace T)).property N)
    (τ : N.sections)
    [AlgebraicGeometry.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj T).sheaf.obj
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.property
      (representedRestriction B S hS T N)] :
    schemeSpaceIdeal B S hS T (zeroScheme B S hS (schemeSpace T) N τ) =
      Stacks.Divisors.zeroScheme ((BigFppfOver.toScheme B S hS).obj T)
        (representedRestriction B S hS T N) (representedRestrictionSection B S hS T N τ) := by
  ext O : 2
  rw [Stacks.Divisors.zeroScheme_ideal]
  have hL := ideal_ker_closedSubspaceBaseChangeChartProj_zeroScheme B S hS (schemeSpace T)
    N hinv τ (selfChart B S hS T) O
  show (closedSubspaceBaseChangeChartProj B S hS (isAlgebraicSpace_yoneda B S hS T)
      (zeroScheme B S hS (schemeSpace T) N τ).1
      (zeroScheme B S hS (schemeSpace T) N τ).2 (selfChart B S hS T)).ker.ideal O = _
  refine hL.trans ?_
  set A := openChart B S hS (schemeSpace T).obj (selfChart B S hS T) O.1
  set x := τ.eval (op A)
  set c := chartSectionsToRestrict (schemeSpace T) N (selfChart B S hS T) O.1
  set ρ := openChartTopRingHom B S hS (schemeSpace T) (selfChart B S hS T) O.1
  set ρ' := ((chartSchemeRestrictionRingHom B S hS (schemeSpace T).obj
    (selfChart B S hS T)).app (op O.1)).hom
  have hpre : ∀ {U V : (((BigFppfOver.toScheme B S hS).obj T).Opens)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ U)
      (r : ((BigFppfOver.toScheme B S hS).obj T).presheaf.obj V),
      ((BigFppfOver.toScheme B S hS).obj T).presheaf.map f
        (((BigFppfOver.toScheme B S hS).obj T).presheaf.map g r) = r := by
    intro U V f g r
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ f) (𝟙 V)]
    simp
  have hρρ' : ∀ r, ρ (ρ' r) = r := fun r => hpre _ _ r
  have hρ'ρ : ∀ a, ρ' (ρ a) = a := fun a => hpre _ _ a
  have hρρ'' : ∀ r : Γ((BigFppfOver.toScheme B S hS).obj T, O.1), ρ (ρ' r) = r :=
    fun r => hpre _ _ r
  have hσ : (representedRestriction B S hS T N).presheaf.map (homOfLE le_top).op
      (representedRestrictionSection B S hS T N τ) = c x := by
    have h := chartSectionsToRestrict_naturality (schemeSpace T) N (selfChart B S hS T)
      (homOfLE (le_top : O.1 ≤ ⊤)) (τ.eval (op (openChart B S hS (yoneda.obj T)
        (selfChart B S hS T) ⊤)))
    refine h.trans (congrArg c ?_)
    exact PresheafOfModules.sections_property τ _
  have hbij := bijective_chartSectionsToRestrict (schemeSpace T) N (selfChart B S hS T) O.1
  have hsmul := chartSectionsToRestrict_smul (schemeSpace T) N (selfChart B S hS T) O.1
  let e := AddEquiv.ofBijective c hbij
  have he : ∀ y, c (e.symm y) = y := fun y => e.apply_symm_apply y
  have hes : ∀ r y, e.symm (r • y) = (show chartRing B S hS (schemeSpace T).obj
      (isAlgebraicSpace_yoneda B S hS T) A from ρ' r) • e.symm y := by
    intro r y
    apply hbij.1
    rw [he, hsmul, he]
  apply le_antisymm
  · refine Ideal.map_le_of_le_comap ?_
    refine Ideal.span_le.2 ?_
    rintro _ ⟨l, rfl⟩
    let φ : (representedRestriction B S hS T N).val.obj (op O.1)
        →ₗ[Γ((BigFppfOver.toScheme B S hS).obj T, O.1)]
        Γ((BigFppfOver.toScheme B S hS).obj T, O.1) :=
      { toFun := fun y => ρ (l (e.symm y))
        map_add' := fun y y' =>
          (congrArg (fun t => ρ (l t)) (e.symm.map_add y y')).trans
            ((congrArg ρ (l.map_add _ _)).trans (ρ.map_add _ _))
        map_smul' := fun r y => by
          show ρ (l (e.symm (r • y))) = _
          refine (congrArg (fun t => ρ (l t)) (hes r y)).trans ?_
          refine (congrArg ρ (l.map_smul _ _)).trans ?_
          refine (ρ.map_mul (ρ' r) (l (e.symm y))).trans ?_
          rw [hρρ'' r]
          rfl }
    refine Ideal.mem_comap.2 (Ideal.subset_span ⟨φ, ?_⟩)
    rw [hσ]
    show ρ (l x) = ρ (l (e.symm (c x)))
    rw [show e.symm (c x) = x from e.symm_apply_apply x]
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨φ, rfl⟩
    rw [hσ]
    rw [← hρρ' (φ (c x))]
    refine Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨
      { toFun := fun z => ρ' (φ (c z))
        map_add' := fun z z' =>
          (congrArg (fun t => ρ' (φ t)) (c.map_add z z')).trans
            ((congrArg ρ' (φ.map_add _ _)).trans (ρ'.map_add _ _))
        map_smul' := fun a z => by
          show ρ' (φ (c (a • z))) = _
          have ha := hsmul (ρ a) z
          have hca : c (a • z) = (show (chartScheme (selfChart B S hS T)).ringCatSheaf.obj.obj
              (op O.1) from ρ a) • c z := by
            rw [← ha]
            exact congrArg c (congrArg (· • z) (hρ'ρ a).symm)
          refine (congrArg (fun t => ρ' (φ t)) hca).trans ?_
          refine (congrArg ρ' (φ.map_smul _ _)).trans ?_
          refine (ρ'.map_mul (ρ a) (φ (c z))).trans ?_
          simp only [hρ'ρ, RingHom.id_apply]
          rfl }, rfl⟩)

/-- **Every global section of the restriction to `T` comes from a global section on `h_T`**: the
étale chart of `h_T` cut out by the top open of `T` is terminal, and its sections are the sections
of the restriction over the top open. -/
theorem exists_representedRestrictionSection_eq
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (σ : Γ(representedRestriction B S hS T N, ⊤)) :
    ∃ τ : N.sections, representedRestrictionSection B S hS T N τ = σ := by
  obtain ⟨x, hx⟩ := (bijective_chartSectionsToRestrict (schemeSpace T) N (selfChart B S hS T) ⊤).2 σ
  have hA : IsTerminal (openChart B S hS (yoneda.obj T) (selfChart B S hS T) ⊤) :=
    (isTerminal_idChart B S hS T).ofIso (openChartTopIso B S hS _ (selfChart B S hS T)).symm
  refine ⟨(Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hA).symm x, ?_⟩
  show chartSectionsToRestrict (schemeSpace T) N (selfChart B S hS T) ⊤
    ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hA)
      ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hA).symm x)) = σ
  exact (congrArg (chartSectionsToRestrict (schemeSpace T) N (selfChart B S hS T) ⊤)
    (Equiv.apply_symm_apply _ x)).trans hx

end AlgebraicGeometry.Space.PrivateChern

end
