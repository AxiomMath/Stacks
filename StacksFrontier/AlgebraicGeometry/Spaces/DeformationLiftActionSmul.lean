module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionNaturality

/-!
# The restriction law of the action of Stacks 061C is semilinear

Let `ψ : W₂ ⟶ W` be a morphism over `X'` and let thickenings `ZU ⊂ W`, `ZV ⊂ W₂` lie over a closed
subspace `Z ⊂ X'`, with an étale morphism `r : ZV ⟶ ZU` over `ψ`
(`AlgebraicGeometry.Space.comp_derivationMove_restriction`). If the restriction law
`ψ ≫ (θ · c) = θ₂ · (ψ ≫ c)` holds, then it holds for `θ` multiplied by a global regular function
`s` of `ZU` and `θ₂` multiplied by `r^*s`
(`AlgebraicGeometry.Space.comp_derivationMove_smul_of_comp_derivationMove`): the restriction of
sections is semilinear over the pullback of functions. Multiplication is
`AlgebraicGeometry.Space.globalFunctionsSmul` on the target `𝒞`.

The formula of the restricted section is the right-hand side of the hypothesis of
`AlgebraicGeometry.Space.comp_derivationMove_restriction`; it is used here only as produced by that
lemma itself, so that no second spelling of it ever meets the first.

## References

* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 0CK8](https://stacks.math.columbia.edu/tag/0CK8)
* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

attribute [local irreducible] modulePullback

/-- Transport along two isomorphisms of a morphism followed by multiplication by `s` is the
transport followed by multiplication by `s`. -/
theorem homCongr_comp_globalFunctionsSmul {X : AlgebraicSpaces C S hS}
    {A A' N N' : Modules.{u, u} C S hS X.1 X.2} (a : A ≅ A') (b : N ≅ N') (θ : A ⟶ N)
    (s : globalFunctions' C S hS X.1) :
    Iso.homCongr a b (θ ≫ globalFunctionsSmul C S hS s N) =
      Iso.homCongr a b θ ≫ globalFunctionsSmul C S hS s N' := by
  simp only [Iso.homCongr_apply, Category.assoc, comp_globalFunctionsSmul,
    comp_globalFunctionsSmul_assoc]

/-- The inverse transport along two isomorphisms of a morphism followed by multiplication by `s`
is the inverse transport followed by multiplication by `s`. -/
theorem homCongr_symm_comp_globalFunctionsSmul {X : AlgebraicSpaces C S hS}
    {A A' N N' : Modules.{u, u} C S hS X.1 X.2} (a : A ≅ A') (b : N ≅ N') (θ : A' ⟶ N')
    (s : globalFunctions' C S hS X.1) :
    (Iso.homCongr a b).symm (θ ≫ globalFunctionsSmul C S hS s N') =
      (Iso.homCongr a b).symm θ ≫ globalFunctionsSmul C S hS s N := by
  rw [Iso.homCongr_symm]
  exact homCongr_comp_globalFunctionsSmul C S hS a.symm b.symm θ s

/-- **The restricted reading of Stacks 03LU is semilinear along an étale restriction**: the
reading `factorForm ∘ p^*` of `w ≫ s` is the reading of `w` followed by `p^*s`. -/
theorem restrictForm_comp_globalFunctionsSmul {P Q A : AlgebraicSpaces C S hS} (p : P ⟶ Q)
    (hp : IsEtale C S hS p.hom) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r)
    {M N : Modules.{u, u} C S hS A.1 A.2}
    (w : (modulePullback C S hS k).obj M ⟶ (modulePullback C S hS k).obj N)
    (s : globalFunctions' C S hS Q.1) :
    QuasiCoherentDescent.restrictForm C S hS p k r hr
        (w ≫ globalFunctionsSmul C S hS s ((modulePullback C S hS k).obj N)) =
      QuasiCoherentDescent.restrictForm C S hS p k r hr w ≫
        globalFunctionsSmul C S hS (globalFunctionsMap C S hS p s)
          ((modulePullback C S hS r).obj N) := by
  rw [QuasiCoherentDescent.restrictForm_eq, QuasiCoherentDescent.restrictForm_eq,
    QuasiCoherentDescent.factorForm, QuasiCoherentDescent.factorForm, Functor.map_comp,
    modulePullback_map_globalFunctionsSmul C S hS p hp]
  simp only [Category.assoc, comp_globalFunctionsSmul, comp_globalFunctionsSmul_assoc]

/-- **The restriction law of the action of Stacks 061C is semilinear.** In the situation of
`AlgebraicGeometry.Space.comp_derivationMove_restriction`, with the restriction `r : ZV ⟶ ZU`
étale: if `ψ ≫ (θ · c) = θ₂ · (ψ ≫ c)`, then `ψ ≫ ((θ s) · c) = (θ₂ (r^*s)) · (ψ ≫ c)` for every
global regular function `s` on `ZU`, the products being multiplication on `𝒞`. -/
theorem comp_derivationMove_smul_of_comp_derivationMove {X' Y' T W W₂ : AlgebraicSpaces C S hS}
    (Z : ClosedSubspaces C S hS X'.1) (ZH : ClosedSubspaces C S hS Y'.1)
    (ZU : ClosedSubspaces C S hS W.1) (ZV : ClosedSubspaces C S hS W₂.1)
    (ψ : W₂ ⟶ W) (φ : W ⟶ X') (φ₂ : W₂ ⟶ X') (hφ : ψ ≫ φ = φ₂)
    (pU : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨Z.1.toFunctor, Z.2.1⟩)
    (pV : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨Z.1.toFunctor, Z.2.1⟩)
    (hsqV : subspaceInclusion C S hS W₂ ZV ≫ φ₂ = pV ≫ subspaceInclusion C S hS X' Z)
    (α : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨ZH.1.toFunctor, ZH.2.1⟩ : AlgebraicSpaces C S hS))
    (q : Y' ⟶ T) (pX' : X' ⟶ T)
    (hZU : IsFirstOrderThickening C S hS W ZU.1) (hZV : IsFirstOrderThickening C S hS W₂ ZV.1)
    (hW : IsFirstOrderThickening C S hS Y' ZH.1)
    (r : (⟨ZV.1.toFunctor, ZV.2.1⟩ : AlgebraicSpaces C S hS) ⟶ ⟨ZU.1.toFunctor, ZU.2.1⟩)
    (hr : subspaceInclusion C S hS W₂ ZV ≫ ψ = r ≫ subspaceInclusion C S hS W ZU)
    (hpr : r ≫ pU = pV)
    (eV : (modulePullback C S hS pV).obj (conormalModule C S hS X' Z) ≅
      conormalModule C S hS W₂ ZV)
    (heV : eV.hom = conormalMap C S hS ZV Z φ₂ pV hsqV)
    (c : W ⟶ Y')
    (hc : subspaceInclusion C S hS W ZU ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) ≫
      subspaceInclusion C S hS Y' ZH)
    (hcq : c ≫ q = φ ≫ pX')
    (hc₂ : subspaceInclusion C S hS W₂ ZV ≫ ψ ≫ c =
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) ≫
      subspaceInclusion C S hS Y' ZH)
    (hcq₂ : (ψ ≫ c) ≫ q = φ₂ ≫ pX')
    (hret : IsEtale C S hS r.hom)
    (θ : (modulePullback C S hS
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α)).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) ⟶
      conormalModule C S hS W ZU)
    (θ₂ : (modulePullback C S hS
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α)).obj
        (sheafOfDifferentials C S hS (subspaceInclusion C S hS Y' ZH ≫ q)) ⟶
      conormalModule C S hS W₂ ZV)
    (s : globalFunctions' C S hS ZU.1.toFunctor)
    (h : ψ ≫ derivationMove C S hS ZU ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) q hZU c hc θ (φ ≫ pX') hcq =
      derivationMove C S hS ZV ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) q hZV (ψ ≫ c) hc₂ θ₂
        (φ₂ ≫ pX') hcq₂) :
    ψ ≫ derivationMove C S hS ZU ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) q hZU c hc
        (θ ≫ globalFunctionsSmul C S hS (X := ⟨ZU.1.toFunctor, ZU.2.1⟩) s
          (conormalModule C S hS W ZU)) (φ ≫ pX') hcq =
      derivationMove C S hS ZV ZH
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) q hZV (ψ ≫ c) hc₂
        (θ₂ ≫ globalFunctionsSmul C S hS (X := ⟨ZV.1.toFunctor, ZV.2.1⟩)
          (globalFunctionsMap C S hS r s) (conormalModule C S hS W₂ ZV))
        (φ₂ ≫ pX') hcq₂ := by
  subst hφ
  have hfc : @CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ r
      (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) =
        (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ α) hpr)
  have key := fun θ₀ θ' hθ' => comp_derivationMove_of_eq C S hS ZV ZU ZH ψ r
    (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pU α) hr q hZV hZU hW c hc θ₀
    (φ ≫ pX') hcq (@CategoryStruct.comp (AlgebraicSpaces C S hS) _ _ _ _ pV α) hfc hc₂ θ' hθ'
    ((ψ ≫ φ) ≫ pX') (Category.assoc _ _ _).symm hcq₂
  have u1 := derivationMove_injective C S hS ZV ZH _ q hZV hW _ hc₂ _ hcq₂ _ _
    (h.symm.trans (key θ _ rfl))
  refine key _ _ ?_
  have k := modulePullback_map_globalFunctionsSmul C S hS (X := ⟨ZU.1.toFunctor, ZU.2.1⟩) r hret s
    (conormalModule C S hS W ZU)
  have k' := comp_globalFunctionsSmul C S hS (X := ⟨ZV.1.toFunctor, ZV.2.1⟩)
    (globalFunctionsMap C S hS r s) (conormalMap C S hS ZV ZU ψ r hr)
  rw [u1, Functor.map_comp, k]
  simp only [Category.assoc, k']

end AlgebraicGeometry.Space
