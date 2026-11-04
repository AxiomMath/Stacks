module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormulaLeft
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.DerivedTwistDetection
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormula
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDiagonalEquivalence

/-!
# The negative tensor powers of an ample module detect the zero object of `D_QCoh(𝒪_X)`

Let `X` be a scheme with affine diagonal and `L` an ample invertible `𝒪_X`-module. This file
proves that an object `K` of `D(𝒪_X)` with quasi-coherent cohomology sheaves, such that every
morphism `L ^⊗ (-p)[-j] ⟶ K`, `p ≥ 0`, `j : ℤ`, vanishes, is zero. As
`Hom(L ^⊗ (-p)[-j], K) = Hʲ(X, K ⊗^𝐋 L ^⊗ p)`, this is [Stacks, Tag 0BQR].

The proof is the source's. `X` is quasi-compact (it carries an ample invertible module), so by
[Stacks, Tag 08DB] the object `K` is represented by a complex `D` of quasi-coherent modules. If
`Hʲ(D) ≠ 0`, apply to the epimorphism `Zʲ(D) ⟶ Hʲ(D)` the lifting step: a nonzero section of
`Hʲ(D)` on an affine chart `X_s` of an ample section lifts to a cocycle on `X_s`, which
[Stacks, Tag 01PW] extends, after a twist, to a global section of `Zʲ(D) ⊗ L ^⊗ p` whose image in
`Hʲ(D) ⊗ L ^⊗ p` is nonzero. The corresponding morphism `L ^⊗ (-p)[-j] ⟶ D` is nonzero on `Hʲ`.

## Main results

* `Stacks.SectionTensorFormula.whiskerRight_app_tensorSection` — the product of two sections is
  natural in the first factor.
* `Stacks.AmpleNonvanishingChart.exists_hom_tensorPowModule_neg_comp_ne_zero` — an epimorphism
  `Z ⟶ H ≠ 0` of quasi-coherent modules has a morphism `L ^⊗ (-p) ⟶ Z` with nonzero composite.
* `Stacks.AmpleNonvanishingChart.exists_iso_Q_obj_of_quasicoherent` — an object of `D_QCoh(𝒪_X)`
  is a complex of quasi-coherent modules, on a quasi-compact scheme with affine diagonal.
* `Stacks.AmpleNonvanishingChart.isZero_of_forall_hom_tensorPowModule_neg_eq_zero` — the
  detection statement displayed above.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category TopologicalSpace Opposite
open MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules (sheafifyValIso)

universe w v u

namespace Stacks.SectionTensorFormula

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F F' : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

end Site

section Scheme

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

variable {X : Scheme.{u}}

/-- **The product of two sections is natural in the first factor.** -/
theorem whiskerRight_app_tensorSection {F F' : X.Modules} (g : F ⟶ F') (G : X.Modules)
    {U : X.Opens} (m : Γ(F, U)) (n : Γ(G, U)) :
    (g ▷ G).app U (tensorSection F G m n) = tensorSection F' G (g.app U m) n :=
  congrArg (fun α => α.app (op U) (m ⊗ₜ[Γ(X, U)] n))
    (toTensorSection_comp_whiskerRight_val X.presheaf (schemeSheafCondition X) G g)

end Scheme

end Stacks.SectionTensorFormula

namespace Stacks.AmpleNonvanishingChart

open Stacks.Ample Stacks.SectionTensorFormula
open Stacks.SectionExtension (resTop)

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- Whiskering a morphism to the unit and then cancelling it by the right unitor commutes with a
morphism in the first variable. -/
theorem whiskerLeft_comp_rightUnitor_hom_comp {C : Type*} [Category C] [MonoidalCategory C]
    {F F' A : C} (e : A ⟶ 𝟙_ C) (π : F ⟶ F') :
    F ◁ e ≫ (ρ_ F).hom ≫ π = π ▷ A ≫ F' ◁ e ≫ (ρ_ F').hom := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality]

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The untwisting is natural in the target.** -/
theorem homTensorPowModuleNegOfUnitHom_comp {F F' : X.Modules} (p : ℤ)
    (g : 𝟙_ X.Modules ⟶ F ⊗ tensorPowModule X L p) (π : F ⟶ F') :
    homTensorPowModuleNegOfUnitHom L F p g ≫ π =
      homTensorPowModuleNegOfUnitHom L F' p (g ≫ π ▷ tensorPowModule X L p) := by
  have key : (α_ F (tensorPowModule X L p) (tensorPowModule X L (-p))).hom ≫
      F ◁ (SheafOfModules.tensorPowMulNegIso X.presheaf
        (Stacks.AmpleGlobalGeneration.sheafCondition X) L p).hom ≫ (ρ_ F).hom ≫ π =
      (π ▷ tensorPowModule X L p) ▷ tensorPowModule X L (-p) ≫
        (α_ F' (tensorPowModule X L p) (tensorPowModule X L (-p))).hom ≫
          F' ◁ (SheafOfModules.tensorPowMulNegIso X.presheaf
            (Stacks.AmpleGlobalGeneration.sheafCondition X) L p).hom ≫ (ρ_ F').hom := by
    rw [associator_naturality_left_assoc]
    exact whisker_eq _ (whiskerLeft_comp_rightUnitor_hom_comp _ π)
  simp only [homTensorPowModuleNegOfUnitHom, Stacks.AmpleGlobalGeneration.twistCancelIso,
    Iso.trans_hom, Functor.map_comp, Category.assoc]
  exact congrArg (fun k => (λ_ (tensorPowModule X L (-p))).inv ≫
    (MonoidalCategory.tensorRight (tensorPowModule X L (-p))).map g ≫ k) key

/-- **A nonzero quotient of a quasi-coherent module is seen by a negative twist through the
module.** Let `L` be an ample invertible `𝒪_X`-module and `π : Z ⟶ H` an epimorphism of
quasi-coherent `𝒪_X`-modules with `H ≠ 0`. Then some morphism `L ^⊗ (-p) ⟶ Z`, `p ≥ 0`, has
nonzero composite with `π`.

This is the lifting step of [Stacks, Tag 0BQR]: choose a point where `H` has a nonzero stalk, an
affine chart `X_s` of an ample section around it and a nonzero section `t` of `H` over `X_s`;
lift `t` to a section `t'` of `Z` over `X_s`, sections over an affine open being exact on
quasi-coherent modules; extend `t' ⊗ σ` to a global section `τ'` of `Z ⊗ L ^⊗ p` by
[Stacks, Tag 01PW]; then the image of `τ'` in `H ⊗ L ^⊗ p` restricts on `X_s` to `t ⊗ σ ≠ 0`,
and untwisting the morphism `𝒪_X ⟶ Z ⊗ L ^⊗ p` that `τ'` defines gives the required morphism. -/
theorem exists_hom_tensorPowModule_neg_comp_ne_zero (hL : IsAmple X L) {Z H : X.Modules}
    [Z.IsQuasicoherent] [H.IsQuasicoherent] (π : Z ⟶ H) [Epi π] (hH : ¬ IsZero H) :
    ∃ (p : ℕ) (ψ : tensorPowModule X L (-(p : ℤ)) ⟶ Z), ψ ≫ π ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_point_not_isZero_stalk H hH
  obtain ⟨n, hn, s, haff, hxs⟩ :=
    Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen X L hL x
  obtain ⟨t, ht⟩ := exists_section_ne_zero_of_isAffineOpen H _ haff x hxs hx
  obtain ⟨t', ht'⟩ := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X π _ haff t
  have ht'' : π.app _ t' = t := ht'
  obtain ⟨p, σ, τ', hopen, heq⟩ :=
    Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple L hL Z hn s t'
  let g : 𝟙_ X.Modules ⟶ Z ⊗ tensorPowModule X L (p : ℤ) :=
    (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).symm τ'
  refine ⟨p, homTensorPowModuleNegOfUnitHom L Z p g, ?_⟩
  rw [homTensorPowModuleNegOfUnitHom_comp]
  refine homTensorPowModuleNegOfUnitHom_ne_zero L H p _ fun h0 => ht ?_
  have hτ : (π ▷ tensorPowModule X L (p : ℤ)).app ⊤ τ' = 0 := by
    have h2 : Stacks.SectionProduct.globalSection X _ g = τ' :=
      (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).apply_symm_apply τ'
    have h1 := Stacks.SectionProduct.globalSection_comp _ _ g (π ▷ tensorPowModule X L (p : ℤ))
    rw [h0, h2] at h1
    rw [← h1]
    exact map_zero (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _)
  refine Stacks.SectionProduct.eq_zero_of_tensorSection_eq_zero H
    (tensorPowModule X L (p : ℤ)) σ (fun y hy => ?_) ?_
  · rwa [hopen] at hy
  · have e1 := whiskerRight_app_tensorSection π (tensorPowModule X L (p : ℤ)) t'
      (resTop (Stacks.AmpleTheory.powNonvanishingOpen X L n s) σ)
    rw [← heq] at e1
    rw [← ht'']
    refine e1.symm.trans ?_
    refine (PresheafOfModules.naturality_apply (π ▷ tensorPowModule X L (p : ℤ)).val
      (homOfLE (le_top : Stacks.AmpleTheory.powNonvanishingOpen X L n s ≤ ⊤)).op τ').trans ?_
    rw [show (π ▷ tensorPowModule X L (p : ℤ)).val.app (op ⊤) τ' = 0 from hτ, map_zero]
    rfl

/-! ### Complexes of quasi-coherent modules -/

open Stacks.AlgebraicGeometry.QuasicoherentDerived in
/-- **An object of `D_QCoh(𝒪_X)` is represented by a complex of quasi-coherent modules**, on a
quasi-compact scheme with affine diagonal. This is the essential surjectivity half of
[Stacks, Tag 08DB]: the comparison functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` is an equivalence, and
every object of `D(QCoh(𝒪_X))` is a complex of quasi-coherent modules. -/
theorem exists_iso_Q_obj_of_quasicoherent (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) K) :
    ∃ D : CochainComplex X.Modules ℤ, (∀ i, (D.X i).IsQuasicoherent) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj D) := by
  have := Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal X
  let Φ := derivedQuasicoherentComparison.{u} X
  let Y := Φ.objPreimage ⟨K, hK⟩
  let F := DerivedCategory.Q.objPreimage Y
  let ι := (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι
  exact ⟨(ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj F, fun i => (F.X i).property,
    ⟨((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.mapIso
          (Φ.objObjPreimageIso ⟨K, hK⟩)).symm ≪≫
      ι.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso Y).symm ≪≫
      ι.mapDerivedCategoryFactors.app F⟩⟩

/-! ### Stacks Tag 0BQR in Hom shape -/

/-- **The negative tensor powers of an ample invertible module detect the zero object of
`D_QCoh(𝒪_X)`.**

Let `X` be a scheme with affine diagonal, `L` an ample invertible `𝒪_X`-module and `K` an object
of the derived category of `𝒪_X`-modules with quasi-coherent cohomology sheaves. If every
morphism `L ^⊗ (-p)[-j] ⟶ K`, `p ≥ 0`, `j : ℤ`, is zero, then `K` is a zero object. Since
`Hom(L ^⊗ (-p)[-j], K) = Hʲ(X, K ⊗^𝐋 L ^⊗ p)`, this is [Stacks, Tag 0BQR].

The source's proof: `X` is quasi-compact, so by [Stacks, Tag 08DB] `K` is a complex `D` of
quasi-coherent modules. If `Hʲ(D) ≠ 0`, the epimorphism `Zʲ(D) ⟶ Hʲ(D)` of quasi-coherent
modules is seen by a morphism `L ^⊗ (-p) ⟶ Zʲ(D)`
(`Stacks.AmpleNonvanishingChart.exists_hom_tensorPowModule_neg_comp_ne_zero`), and the
corresponding morphism `L ^⊗ (-p)[-j] ⟶ D` is nonzero on `Hʲ`. -/
theorem isZero_of_forall_hom_tensorPowModule_neg_eq_zero
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hL : IsAmple X L) (K : DerivedCategory X.Modules)
    (hKQ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (hvan : ∀ (p : ℕ) (j : ℤ) (φ : (DerivedCategory.singleFunctor X.Modules j).obj
      (tensorPowModule X L (-(p : ℤ))) ⟶ K), φ = 0) :
    IsZero K := by
  have : CompactSpace X := Stacks.Ample.IsAmpleForPowers.compactSpace hL
  obtain ⟨D, hD, ⟨e⟩⟩ := exists_iso_Q_obj_of_quasicoherent X K hKQ
  refine IsZero.of_iso ?_ e
  refine (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun j => ?_
  by_contra hj
  have hH : ¬ IsZero (D.homology j) := fun h =>
    hj (h.of_iso ((DerivedCategory.homologyFunctorFactors X.Modules j).app D))
  have : (D.homology j).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((DerivedCategory.homologyFunctor X.Modules j).mapIso e) ≪≫
        (DerivedCategory.homologyFunctorFactors X.Modules j).app D) (hKQ j)
  have : (D.cycles j).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork
      (D.cyclesIsKernel j (j + 1) (by simp)) (hD j) (hD (j + 1))
  obtain ⟨p, ψ, hψ⟩ := exists_hom_tensorPowModule_neg_comp_ne_zero L hL (D.homologyπ j) hH
  refine DerivedCategory.homFromSingleOfCycles_ne_zero ψ hψ ?_
  exact ((Iso.comp_inv_eq e).1
    (hvan p j (DerivedCategory.homFromSingleOfCycles ψ ≫ e.inv))).trans zero_comp

end Stacks.AmpleNonvanishingChart

end
