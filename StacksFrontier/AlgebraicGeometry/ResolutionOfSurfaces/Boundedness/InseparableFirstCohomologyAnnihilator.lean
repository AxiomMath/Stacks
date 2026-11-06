module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableRestrictionInjective
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpTrace
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# A Frobenius splitting over an open kills `H¹(X, π_* 𝒪_Y)`

Let `π : Y ⟶ X` be a finite surjective morphism of normal integral schemes in characteristic `p`
with `Lᵖ ⊆ K` for their function fields, and let `U ⊆ X` be a nonempty open. Suppose given an
additive `θ : K ⟶ K` which preserves the local ring of `X` at every point of `U` (for `X` a
modification of the spectrum of a complete regular local ring `A` and `U` the inverse image of the
punctured spectrum, a Frobenius splitting of `A` extended to `K`), and global functions
`bᵢ, eᵢ` of `Y` and `d` of `X` with

  `d σ = ∑ᵢ θ((bᵢ σ)ᵖ) eᵢ` for every `σ ∈ L`.

Then multiplication by `d` is zero on `H¹(X, π_* 𝒪_Y)` as soon as `H¹(X, 𝒪_X) = 0` and every
function on `U` extends to `X`.

The proof: after restriction to `U`, multiplication by `d` on `π_* 𝒪_Y` is the sum of the
composites `π_* 𝒪_Y ⟶ 𝒪_X ⟶ j_* j⁻¹ 𝒪_X ⟶ j_* j⁻¹ 𝒪_X ⟶ j_* j⁻¹ π_* 𝒪_Y` (`s ↦ (bᵢ s)ᵖ`,
restriction, `θ`, `t ↦ t eᵢ`) of abelian sheaves; each factors through `H¹(X, 𝒪_X) = 0` on
cohomology, and `H¹(X, π_* 𝒪_Y) ⟶ H¹(X, j_* j⁻¹ π_* 𝒪_Y)` is injective
(`AlgebraicGeometry.SeparableGoUp.mono_rightDerived_one_toRestrictExtend`). The maps `s ↦ sᵖ` and
`θ` are additive but not linear, which is why the argument runs in abelian sheaf cohomology; the
module-valued cohomology is compared with it by [Stacks, Tag 03FD].

This is the cohomological core of the Frobenius route to [Stacks, Tag 0B4U], which replaces the
trace and duality of the source's proof.

## Main results

* `AlgebraicGeometry.SeparableGoUp.thetaHom`: `θ` on `j_* j⁻¹ 𝒪_X`.
* `AlgebraicGeometry.SeparableGoUp.rightDerived_map_smulEnd_eq_zero`: multiplication by `d` is
  zero on `H¹(X, π_* 𝒪_Y)`, in the module-valued cohomology.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SeparableGoUp

open Stacks.Cohomology.RestrictionCover

attribute [local instance] HasDerivedCategory.standard

section Theta

variable {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (θ : X.functionField →+ X.functionField)
  (hθ : ∀ x : X, x ∈ U → ∀ a : X.presheaf.stalk x, ∃ b : X.presheaf.stalk x,
    algebraMap _ X.functionField b = θ (algebraMap _ X.functionField a))

include hθ in
/-- `θ` carries sections of `𝒪_X` over an open contained in `U` to sections. -/
theorem exists_theta_section (V : X.Opens) (hV : V ≤ U) (t : Γ(X, V)) :
    ∃ t' : Γ(X, V), ∀ hη : genericPoint X ∈ V,
      X.presheaf.germ V (genericPoint X) hη t' = θ (X.presheaf.germ V (genericPoint X) hη t) := by
  by_cases hη : genericPoint X ∈ V
  · have : Nonempty V := ⟨⟨_, hη⟩⟩
    obtain ⟨t', ht'⟩ := exists_germToFunctionField_eq_of_forall_mem_range X V
      (θ (X.germToFunctionField V t)) fun x => by
        obtain ⟨b, hb⟩ := hθ x.1 (hV x.2) (X.presheaf.germ V x.1 x.2 t)
        exact ⟨b, by rw [hb, X.algebraMap_germ_eq_germToFunctionField]⟩
    exact ⟨t', fun _ => ht'⟩
  · exact ⟨0, fun h => absurd h hη⟩

/-- The value of `θ` on sections over an open contained in `U`. -/
def thetaApp (V : X.Opens) (hV : V ≤ U) (t : Γ(X, V)) : Γ(X, V) :=
  (exists_theta_section U θ hθ V hV t).choose

/-- The germ of `thetaApp` at the generic point is `θ` of the germ. -/
theorem germ_thetaApp (V : X.Opens) (hV : V ≤ U) (t : Γ(X, V)) (hη : genericPoint X ∈ V) :
    X.presheaf.germ V (genericPoint X) hη (thetaApp U θ hθ V hV t) =
      θ (X.presheaf.germ V (genericPoint X) hη t) :=
  (exists_theta_section U θ hθ V hV t).choose_spec hη

/-- `thetaApp` is additive. -/
theorem thetaApp_add (V : X.Opens) (hV : V ≤ U) (s t : Γ(X, V)) :
    thetaApp U θ hθ V hV (s + t) = thetaApp U θ hθ V hV s + thetaApp U θ hθ V hV t :=
  sections_ext (X := X) _ _ fun hη => by
    rw [map_add, germ_thetaApp, germ_thetaApp, germ_thetaApp, map_add, map_add]

/-- `thetaApp` sends `0` to `0`. -/
theorem thetaApp_zero (V : X.Opens) (hV : V ≤ U) : thetaApp U θ hθ V hV 0 = 0 :=
  sections_ext (X := X) _ _ fun hη => by simp only [germ_thetaApp, map_zero]

/-- `thetaApp` commutes with restriction to a smaller open. -/
theorem thetaApp_res {V V' : X.Opens} (hV : V ≤ U) (i : V' ⟶ V) (t : Γ(X, V)) :
    thetaApp U θ hθ V' (i.le.trans hV) (X.presheaf.map i.op t) =
      X.presheaf.map i.op (thetaApp U θ hθ V hV t) :=
  sections_ext (X := X) _ _ fun hη => by
    rw [germ_thetaApp, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply,
      germ_thetaApp U θ hθ V hV t (i.le hη)]

/-- `θ` as an additive map on sections over an open contained in `U`. -/
def thetaAddHom (V : X.Opens) (hV : V ≤ U) : Γ(X, V) →+ Γ(X, V) where
  toFun := thetaApp U θ hθ V hV
  map_zero' := thetaApp_zero U θ hθ V hV
  map_add' := thetaApp_add U θ hθ V hV

/-- **`θ` on `j_* j⁻¹ 𝒪_X`**, as a morphism of abelian sheaves: on sections over `W` it is `θ` on
the sections of `𝒪_X` over `W ∩ U`. -/
def thetaHom :
    (Opens.restrictExtend U AddCommGrpCat.{u}).obj (unitAb X) ⟶
      (Opens.restrictExtend U AddCommGrpCat.{u}).obj (unitAb X) :=
  ⟨{ app W := AddCommGrpCat.ofHom
        (thetaAddHom U θ hθ _ (Opens.openIntersection_obj_le_right U W.unop))
     naturality {W W'} i := by
       ext t
       exact thetaApp_res U θ hθ (Opens.openIntersection_obj_le_right U W.unop)
         ((openIntersection U).map i.unop) t }⟩

/-- On sections over `W`, `thetaHom` is `thetaApp` on sections over `W ∩ U`. -/
@[simp] theorem thetaHom_app (W : (X.Opens)ᵒᵖ) (t : Γ(X, (openIntersection U).obj W.unop)) :
    (thetaHom U θ hθ).hom.app W t =
      thetaApp U θ hθ _ (Opens.openIntersection_obj_le_right U W.unop) t := rfl

end Theta

/-- The components of a finite sum of morphisms of abelian sheaves are the sums of the
components. -/
theorem sheaf_sum_hom_app {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι) (f : ι → (F ⟶ G)) (W : Cᵒᵖ)
    (x : F.obj.obj W) : (∑ i ∈ s, f i).hom.app W x = ∑ i ∈ s, (f i).hom.app W x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Sheaf.Hom.add_app, AddCommGrpCat.hom_add_apply,
      ih]

section Identity

variable {X Y : Scheme.{u}} (π : Y ⟶ X) (p : ℕ) [Fact p.Prime]
  [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π] [IsNormal X]
  [CharP X.functionField p]
  (hpow : ∀ y : Y.functionField, ∃ k : X.functionField, dominantFunctionFieldMap π k = y ^ p)
  (U : X.Opens) [Nonempty U] (θ : X.functionField →+ X.functionField)
  (hθ : ∀ x : X, x ∈ U → ∀ a : X.presheaf.stalk x, ∃ b : X.presheaf.stalk x,
    algebraMap _ X.functionField b = θ (algebraMap _ X.functionField a))

omit [Nonempty U] in
/-- **Multiplication by `d`, restricted to `U`, factors through the `p`-th power maps.** If
`d σ = ∑ᵢ θ((bᵢ σ)ᵖ) eᵢ` on the function field of `Y`, then on abelian sheaves
`(d ·) ≫ (π_* 𝒪_Y ⟶ j_* j⁻¹ π_* 𝒪_Y)` is the sum over `i` of
`(s ↦ (bᵢ s)ᵖ) ≫ (𝒪_X ⟶ j_* j⁻¹ 𝒪_X) ≫ θ ≫ (t ↦ t eᵢ)`. -/
theorem smulEnd_comp_toRestrictExtend_eq_sum {n : ℕ} (b e : Fin n → Γ(Y, ⊤)) (d : Γ(X, ⊤))
    (h : ∀ (σ : Y.functionField) (k : Fin n → X.functionField),
      (∀ i, dominantFunctionFieldMap π (k i) =
        (Y.presheaf.germ ⊤ (genericPoint Y) trivial (b i) * σ) ^ p) →
      dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial d) * σ =
        ∑ i, dominantFunctionFieldMap π (θ (k i)) *
          Y.presheaf.germ ⊤ (genericPoint Y) trivial (e i)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.smulEnd X d).asHom.app
        ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf))) ≫
      (Opens.toRestrictExtend U AddCommGrpCat.{u}).app (pushforwardUnitAb π) =
    ∑ i, ((SheafOfModules.toSheaf X.ringCatSheaf).map (pushMulHom π (b i)) ≫
      frobeniusHom π p hpow) ≫ ((Opens.toRestrictExtend U AddCommGrpCat.{u}).app (unitAb X) ≫
        thetaHom U θ hθ ≫ (Opens.restrictExtend U AddCommGrpCat.{u}).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (mulHom π (e i)))) := by
  ext W s₀
  rw [sheaf_sum_hom_app]
  let V := (openIntersection U).obj W.unop
  have hVW : V ≤ W.unop := Opens.openIntersection_obj_le U W.unop
  have hVU : V ≤ U := Opens.openIntersection_obj_le_right U W.unop
  let s : Γ(Y, π ⁻¹ᵁ W.unop) := s₀
  show Y.presheaf.map (homOfLE (preimage_openIntersection_le π U W.unop)).op
      (π.app W.unop (resTop X W.unop d) * s) =
    ∑ i, π.app V (thetaApp U θ hθ V hVU (X.presheaf.map (homOfLE hVW).op
      (frobeniusApp π p hpow W.unop (resTop Y (π ⁻¹ᵁ W.unop) (b i) * s)))) *
        resTop Y (π ⁻¹ᵁ V) (e i)
  refine sections_ext_Y _ _ fun hV => ?_
  have hηV : genericPoint X ∈ V := by
    have h' : π (genericPoint Y) ∈ V := hV
    rwa [map_genericPoint π] at h'
  have hηW : genericPoint X ∈ W.unop := hVW hηV
  rw [Y.presheaf.germ_res_apply, map_sum, map_mul, germ_app π W.unop hηW, germ_resTop]
  have hterm : ∀ i, Y.presheaf.germ (π ⁻¹ᵁ V) (genericPoint Y) hV
      (π.app V (thetaApp U θ hθ V hVU (X.presheaf.map (homOfLE hVW).op
        (frobeniusApp π p hpow W.unop (resTop Y (π ⁻¹ᵁ W.unop) (b i) * s)))) *
          resTop Y (π ⁻¹ᵁ V) (e i)) =
      dominantFunctionFieldMap π (θ (X.presheaf.germ W.unop (genericPoint X) hηW
        (frobeniusApp π p hpow W.unop (resTop Y (π ⁻¹ᵁ W.unop) (b i) * s)))) *
        Y.presheaf.germ ⊤ (genericPoint Y) trivial (e i) := fun i => by
    rw [map_mul, germ_app π V hηV, germ_resTop, germ_thetaApp, X.presheaf.germ_res_apply]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  refine h _ _ fun i => ?_
  rw [germ_frobeniusApp, germY, map_mul, germ_resTop]

include hpow hθ in
/-- **Multiplication by `d` is zero on `H¹(X, π_* 𝒪_Y)`, in abelian sheaf cohomology**, when
`H¹(X, 𝒪_X) = 0`, every function on `U` extends to `X`, `Y` is normal and
`d σ = ∑ᵢ θ((bᵢ σ)ᵖ) eᵢ` on the function field of `Y`. -/
theorem rightDerived_map_toSheaf_smulEnd_eq_zero [IsNormal Y] {n : ℕ} (b e : Fin n → Γ(Y, ⊤))
    (d : Γ(X, ⊤))
    (h : ∀ (σ : Y.functionField) (k : Fin n → X.functionField),
      (∀ i, dominantFunctionFieldMap π (k i) =
        (Y.presheaf.germ ⊤ (genericPoint Y) trivial (b i) * σ) ^ p) →
      dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial d) * σ =
        ∑ i, dominantFunctionFieldMap π (θ (k i)) *
          Y.presheaf.germ ⊤ (genericPoint Y) trivial (e i))
    (hX : IsZero (((sectionsAb X).rightDerived 1).obj (unitAb X)))
    (hext : Function.Surjective (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) :
    ((sectionsAb X).rightDerived 1).map ((SheafOfModules.toSheaf X.ringCatSheaf).map
      ((Scheme.smulEnd X d).asHom.app
        ((Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)))) = 0 := by
  have : ((sectionsAb X).rightDerived 1).Additive :=
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (sectionsAb X)).additive 1
  have := mono_rightDerived_one_toRestrictExtend π p hpow U hX hext
  rw [← cancel_mono (((sectionsAb X).rightDerived 1).map
      ((Opens.toRestrictExtend U AddCommGrpCat.{u}).app (pushforwardUnitAb π))), zero_comp,
    ← Functor.map_comp, smulEnd_comp_toRestrictExtend_eq_sum π p hpow U θ hθ b e d h,
    Functor.map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Functor.map_comp, hX.eq_zero_of_tgt (((sectionsAb X).rightDerived 1).map _), zero_comp]

end Identity

section ModuleComparison

variable (X : Scheme.{u})

/-- **The module-valued and the abelian first cohomology agree** ([Stacks, Tag 03FD]), naturally
in the sheaf of modules: forgetting the module structure on `H¹(X, ℱ)` gives the first cohomology
of the underlying abelian sheaf. -/
def firstCohomologyForgetIso :
    (Scheme.sectionsFunctor X).rightDerived 1 ⋙
        forget₂ (ModuleCat.{u} (Scheme.sectionsRing X)) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙ (sectionsAb X).rightDerived 1 :=
  Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ 1 ≪≫
    Stacks.Cohomology.ModuleComparison.underlyingSectionsIso X.ringCatSheaf ⊤ 1

/-- A morphism of sheaves of modules inducing zero on abelian first cohomology induces zero on
module-valued first cohomology. -/
theorem rightDerived_map_eq_zero_of_toSheaf {M N : SheafOfModules.{u} X.ringCatSheaf}
    (φ : M ⟶ N)
    (h : ((sectionsAb X).rightDerived 1).map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) = 0) :
    ((Scheme.sectionsFunctor X).rightDerived 1).map φ = 0 := by
  apply (forget₂ (ModuleCat.{u} (Scheme.sectionsRing X)) AddCommGrpCat.{u}).map_injective
  have hn := (firstCohomologyForgetIso X).hom.naturality φ
  simp only [Functor.comp_map] at hn
  have : Mono ((firstCohomologyForgetIso X).hom.app N) :=
    inferInstanceAs (Mono ((firstCohomologyForgetIso X).app N).hom)
  rw [(forget₂ (ModuleCat.{u} (Scheme.sectionsRing X)) AddCommGrpCat.{u}).map_zero,
    ← cancel_mono ((firstCohomologyForgetIso X).hom.app N), hn, h, comp_zero,
    zero_comp]

/-- `H¹(X, 𝒪_X) = 0` in the module-valued cohomology gives it in abelian sheaf cohomology. -/
theorem isZero_rightDerived_unitAb
    (h : IsZero (((Scheme.sectionsFunctor X).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsZero (((sectionsAb X).rightDerived 1).obj (unitAb X)) :=
  ((forget₂ (ModuleCat.{u} (Scheme.sectionsRing X)) AddCommGrpCat.{u}).map_isZero h).of_iso
    ((firstCohomologyForgetIso X).app (SheafOfModules.unit X.ringCatSheaf)).symm

end ModuleComparison

end AlgebraicGeometry.SeparableGoUp

end
