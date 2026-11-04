module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.StageDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage

/-!
# Morphisms out of a finitely presented sheaf of modules into a filtered system

Let `j : W ⟶ X` be étale. The extension by zero `j_! Λ` of the constant sheaf `Λ` corepresents
sections over `W`: `Hom(j_! Λ, H) = H(W)`, naturally in `H`. Consequently, if a sheaf of modules
`F` on `X_étale` is a quotient of a finite direct sum of such sheaves at affine `W`, with kernel
again such a quotient, then a morphism from `F` into the direct image `f_* 𝓛_Y(M)` along a limit
`Y = lim Y_i` of finite morphisms factors through the direct image along some stage `Y_i`. The
sections over the affine `W` are the filtered colimit of those of the stages
(`Stacks.EtaleCohomology.IntegralLimitPresentation.exists_stageMap_app_eq`), and a finite
presentation turns this into a statement about morphisms.

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroConstantHomEquiv` — `Hom(j_! Λ, H) ≃ H(W)`.

## Main results

* `Stacks.EtaleCohomology.IntegralLimitPresentation.exists_comp_stageMap_eq` — the
  factorization through a stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The étale `X`-scheme `W` attached to an étale morphism `j : W ⟶ X`, as the image of the final
object of the small étale site of `W` under composition with `j`. -/
abbrev etaleObjOfEtale {W X : Scheme.{u}} (j : W ⟶ X) [Etale j] : X.Etale :=
  (Scheme.Etale.smallEtaleCompose j).obj (etaleSiteTerminal W)

/-- **`j_! Λ` corepresents sections over `W`.** For an étale `j : W ⟶ X` and a sheaf of modules
`H` on `X_étale`, `Hom(j_! Λ, H) ≃ H(W)`. -/
def extensionByZeroConstantHomEquiv {W X : Scheme.{u}} (j : W ⟶ X) [Etale j]
    (H : EtaleModules.{u, u + 1} Λ X) :
    ((etaleModuleExtensionByZero.{u, u + 1} Λ j).obj
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ)) ⟶ H) ≃
      H.obj.obj (op (etaleObjOfEtale j)) :=
  ((etaleModuleExtensionByZeroAdj.{u, u + 1} Λ j).homEquiv _ _).trans <|
    ((constantSheafAdj W.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (etaleSiteTerminalIsTerminal W)).homEquiv _ _).trans <|
    ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf Λ Λ _).toEquiv

/-- The equivalence `Hom(j_! Λ, H) ≃ H(W)` is natural in `H`. -/
theorem extensionByZeroConstantHomEquiv_comp {W X : Scheme.{u}} (j : W ⟶ X) [Etale j]
    {H H' : EtaleModules.{u, u + 1} Λ X}
    (φ : (etaleModuleExtensionByZero.{u, u + 1} Λ j).obj
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ)) ⟶ H) (ψ : H ⟶ H') :
    extensionByZeroConstantHomEquiv Λ j H' (φ ≫ ψ) =
      ψ.hom.app (op (etaleObjOfEtale j)) (extensionByZeroConstantHomEquiv Λ j H φ) := by
  simp only [extensionByZeroConstantHomEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_right]
  rfl

/-- The equivalence `Hom(j_! Λ, H) ≃ H(W)` sends zero to zero. -/
theorem extensionByZeroConstantHomEquiv_zero {W X : Scheme.{u}} (j : W ⟶ X) [Etale j]
    (H : EtaleModules.{u, u + 1} Λ X) :
    extensionByZeroConstantHomEquiv Λ j H 0 = 0 := by
  have h := extensionByZeroConstantHomEquiv_comp Λ j (0 : _ ⟶ H) (0 : H ⟶ H)
  rw [comp_zero] at h
  rw [h]
  rfl

/-- The sheaf `j_! Λ` for an étale `j`. -/
abbrev extensionByZeroConstant {W X : Scheme.{u}} (j : W ⟶ X) [Etale j] :
    EtaleModules.{u, u + 1} Λ X :=
  (etaleModuleExtensionByZero.{u, u + 1} Λ j).obj
    ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))

namespace IntegralLimitPresentation

attribute [local instance] moduleCat_hasLimitsOfSize
attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

attribute [local instance] AlgebraicGeometry.IntegralLimitPresentation.indexPreorder
  AlgebraicGeometry.IntegralLimitPresentation.indexNonempty
  AlgebraicGeometry.IntegralLimitPresentation.indexDirected

variable (M : Type (u + 1)) [AddCommGroup M] [Module Λ M]
  {X Y : Scheme.{u}} {f : Y ⟶ X} (P : AlgebraicGeometry.IntegralLimitPresentation f)

private instance isAffine_left_etaleObjOfEtale {W X : Scheme.{u}} (j : W ⟶ X) [Etale j]
    [IsAffine W] : IsAffine (etaleObjOfEtale j).left :=
  inferInstanceAs (IsAffine W)

/-- Two morphisms out of a finite direct sum of the sheaves `j_{k,!} Λ` are equal if they agree
on `H(W_k)` under `Hom(j_{k,!} Λ, H) ≃ H(W_k)`. -/
private theorem sigma_hom_ext_extensionByZeroConstantHomEquiv {n : ℕ} {Wd : Fin n → Scheme.{u}}
    (e : ∀ k, Wd k ⟶ X) [∀ k, Etale (e k)] {H : EtaleModules.{u, u + 1} Λ X}
    {a b : (∐ fun k => extensionByZeroConstant Λ (e k)) ⟶ H}
    (h : ∀ k, extensionByZeroConstantHomEquiv Λ (e k) H
      (Sigma.ι (fun k => extensionByZeroConstant Λ (e k)) k ≫ a) =
      extensionByZeroConstantHomEquiv Λ (e k) H
        (Sigma.ι (fun k => extensionByZeroConstant Λ (e k)) k ≫ b)) : a = b :=
  Sigma.hom_ext _ _ fun k => (extensionByZeroConstantHomEquiv Λ (e k) H).injective (h k)

/-- A morphism out of a finite direct sum of the sheaves `j_{k,!} Λ` at affine étale `X`-schemes
into `f_* 𝓛_Y(M)` factors through `f_{i,*} 𝓛_{Y_i}(M)` for some stage `Y_i`. -/
theorem exists_sigma_comp_stageMap_eq {n : ℕ} {Wd : Fin n → Scheme.{u}} (e : ∀ k, Wd k ⟶ X)
    [∀ k, Etale (e k)] [∀ k, IsAffine (Wd k)]
    (χ : (∐ fun k => extensionByZeroConstant Λ (e k)) ⟶
      (etaleModuleDirectImage.{u, u + 1} Λ f).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y M)) :
    ∃ (i : P.indexTypeᵒᵖ) (ψ : (∐ fun k => extensionByZeroConstant Λ (e k)) ⟶
        (etaleModuleDirectImage.{u, u + 1} Λ (stage P i)).obj
          (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ (P.diagram.obj i) M)),
      ψ ≫ stageMap Λ M P i = χ := by
  classical
  let σ : ∀ k, _ := fun k => extensionByZeroConstantHomEquiv Λ (e k) _
    (Sigma.ι (fun k => extensionByZeroConstant Λ (e k)) k ≫ χ)
  choose i τ hτ using fun k => exists_stageMap_app_eq Λ M P _ (σ k)
  obtain ⟨i₀, hi₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let g : ∀ k, i₀ ⟶ i k := fun k => (hi₀ (Finset.mem_image_of_mem i (Finset.mem_univ k))).some
  let τ₀ : ∀ k, _ := fun k => (transitionMap Λ M P (g k)).hom.app _ (τ k)
  have hτ₀ : ∀ k, (stageMap Λ M P i₀).hom.app _ (τ₀ k) = σ k := fun k => by
    rw [← hτ k, ← transitionMap_comp_stageMap Λ M P (g k)]
    rfl
  refine ⟨i₀, Sigma.desc fun k => (extensionByZeroConstantHomEquiv Λ (e k) _).symm (τ₀ k), ?_⟩
  refine sigma_hom_ext_extensionByZeroConstantHomEquiv Λ e fun k => ?_
  rw [Sigma.ι_desc_assoc, extensionByZeroConstantHomEquiv_comp, Equiv.apply_symm_apply, hτ₀]

/-- A morphism out of a finite direct sum of the sheaves `j_{l,!} Λ` at affine étale `X`-schemes
into a stage `f_{i₀,*} 𝓛_{Y_{i₀}}(M)` that vanishes in `f_* 𝓛_Y(M)` already vanishes at some
later stage. -/
theorem exists_comp_transitionMap_eq_zero {m : ℕ} {Wd' : Fin m → Scheme.{u}}
    (e' : ∀ l, Wd' l ⟶ X) [∀ l, Etale (e' l)] [∀ l, IsAffine (Wd' l)] {i₀ : P.indexTypeᵒᵖ}
    (χ : (∐ fun l => extensionByZeroConstant Λ (e' l)) ⟶
      (etaleModuleDirectImage.{u, u + 1} Λ (stage P i₀)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ (P.diagram.obj i₀) M))
    (hχ : χ ≫ stageMap Λ M P i₀ = 0) :
    ∃ (i₁ : P.indexTypeᵒᵖ) (γ₀ : i₁ ⟶ i₀), χ ≫ transitionMap Λ M P γ₀ = 0 := by
  classical
  let ν : ∀ l, _ := fun l => extensionByZeroConstantHomEquiv Λ (e' l) _
    (Sigma.ι (fun l => extensionByZeroConstant Λ (e' l)) l ≫ χ)
  have hν : ∀ l, (stageMap Λ M P i₀).hom.app _ (ν l) = (stageMap Λ M P i₀).hom.app _ 0 :=
    fun l => by
      rw [map_zero, ← extensionByZeroConstantHomEquiv_comp]
      simp only [Category.assoc, hχ, comp_zero]
      exact extensionByZeroConstantHomEquiv_zero Λ (e' l) _
  choose j γ hγ using fun l => exists_transitionMap_app_eq Λ M P _ (ν l) 0 (hν l)
  obtain ⟨i₁, hi₁⟩ := IsCofiltered.inf_objs_exists (insert i₀ (Finset.univ.image j))
  let δ : ∀ l, i₁ ⟶ j l := fun l =>
    (hi₁ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem j (Finset.mem_univ l)))).some
  let γ₀ : i₁ ⟶ i₀ := (hi₁ (Finset.mem_insert_self _ _)).some
  have hγ₀ : ∀ l, (transitionMap Λ M P γ₀).hom.app _ (ν l) = 0 := fun l => by
    rw [show γ₀ = δ l ≫ γ l from Subsingleton.elim _ _, ← transitionMap_comp]
    show (transitionMap Λ M P (δ l)).hom.app _ ((transitionMap Λ M P (γ l)).hom.app _ (ν l)) = 0
    rw [hγ l, map_zero, map_zero]
  refine ⟨i₁, γ₀, sigma_hom_ext_extensionByZeroConstantHomEquiv Λ e' fun l => ?_⟩
  rw [comp_zero, extensionByZeroConstantHomEquiv_zero, ← Category.assoc,
    extensionByZeroConstantHomEquiv_comp]
  exact hγ₀ l

/-- **A morphism out of a finitely presented sheaf into `f_* 𝓛_Y(M)` factors through a stage.**
Let `F` be a quotient `p` of a finite direct sum of the sheaves `j_{k,!} Λ` at affine étale
`X`-schemes, whose kernel is in turn a quotient `q` of such a sum. Every morphism
`F ⟶ f_* 𝓛_Y(M)` factors through `f_{i,*} 𝓛_{Y_i}(M)` for some stage `Y_i`. -/
theorem exists_comp_stageMap_eq {F : EtaleModules.{u, u + 1} Λ X} {n : ℕ}
    {Wd : Fin n → Scheme.{u}} (e : ∀ k, Wd k ⟶ X) [∀ k, Etale (e k)] [∀ k, IsAffine (Wd k)]
    (p : (∐ fun k => extensionByZeroConstant Λ (e k)) ⟶ F) [Epi p] {m : ℕ}
    {Wd' : Fin m → Scheme.{u}} (e' : ∀ l, Wd' l ⟶ X) [∀ l, Etale (e' l)]
    [∀ l, IsAffine (Wd' l)] (q : (∐ fun l => extensionByZeroConstant Λ (e' l)) ⟶ kernel p)
    [Epi q]
    (φ : F ⟶ (etaleModuleDirectImage.{u, u + 1} Λ f).obj
      (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y M)) :
    ∃ (i : P.indexTypeᵒᵖ) (φ' : F ⟶ (etaleModuleDirectImage.{u, u + 1} Λ (stage P i)).obj
        (smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ (P.diagram.obj i) M)),
      φ' ≫ stageMap Λ M P i = φ := by
  obtain ⟨i₀, ψ, hψ⟩ := exists_sigma_comp_stageMap_eq Λ M P e (p ≫ φ)
  obtain ⟨i₁, γ₀, hγ₀⟩ := exists_comp_transitionMap_eq_zero Λ M P e' (q ≫ kernel.ι p ≫ ψ) (by
    simp only [Category.assoc, hψ, kernel.condition_assoc, zero_comp, comp_zero])
  let ψ' := ψ ≫ transitionMap Λ M P γ₀
  have hq : kernel.ι p ≫ ψ' = 0 := by
    rw [← cancel_epi q, comp_zero]
    simpa only [Category.assoc] using hγ₀
  obtain ⟨φ', hφ'⟩ := Cofork.IsColimit.desc'
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)) ψ' (by
      show kernel.ι p ≫ ψ' = 0 ≫ ψ'
      rw [hq, zero_comp])
  refine ⟨i₁, φ', ?_⟩
  rw [← cancel_epi p, ← Category.assoc, show p ≫ φ' = ψ' from hφ', Category.assoc,
    transitionMap_comp_stageMap, hψ]

end IntegralLimitPresentation

end Stacks.EtaleCohomology

end
