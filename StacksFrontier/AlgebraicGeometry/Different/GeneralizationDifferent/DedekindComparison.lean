module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.OneMemComplementaryModule
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.TheDifferent
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.DedekindComparison

/-!
# The generalized different on an affine chart is the Dedekind different

Let `f : Y ⟶ X` be a locally quasi-finite morphism of locally Noetherian schemes with relative
dualizing module `ω_{Y/X}`, let `V = Spec B` and `U = Spec A` be affine opens with
`f(V) ⊆ U`, and suppose the Dedekind different of `A → B` is defined with `1 ∈ L_{B/A}`.  The
generalized different of the section of `ω_{Y/X}` which is `c(1)` on the chart agrees on `V`
with the Dedekind different `𝔇_{B/A}`.

## Main results

* `Stacks.Discriminant.annihilatorSectionCokernel_obj_affine_eq_dedekindDifferentIdeal`: the
  sections over `V` of the annihilator of the cokernel of such a section are `𝔇_{B/A}`.
* `Stacks.Discriminant.exists_sect_annihilatorSectionCokernel_obj_eq_dedekindDifferentIdeal`:
  when the chart is the whole source such a section exists, so the preceding statement is the
  agreement of the two ideal sheaves with no hypothesis on a section.

## Implementation notes

Tag 0BWN states the conclusion as an equality `𝔇_f = (𝔇_{B/A})~` of coherent ideal sheaves on
`Y = Spec B`.  Both are coherent ideal sheaves, and a coherent sheaf on an affine scheme is the
tilde of its module of sections, so that equality is the equality of the two ideals of sections
below; no transport of sheaves along `V ≅ Spec B` is needed.

The section is specified by its image on the chart, which Tag 0BWN identifies with `c(1)`: the
extension of the trace element is unique, so this pins it down.  The hypothesis that the chart
map be flat, which Tag 0BW5 uses to produce the trace element and identify its chart image,
is exactly what is unavailable here and is replaced by that specification.

## References

* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
* [Stacks Project, Tag 0BW5](https://stacks.math.columbia.edu/tag/0BW5)
* [Stacks Project, Tag 0BW3](https://stacks.math.columbia.edu/tag/0BW3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
  RingedSpaceModuleAdjunction TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Discriminant

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

attribute [local instance] algebraDualModule

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf Scheme.Modules

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f]

/-- **[Stacks, Tag 0BWN], agreement of the two differents.** Let `f : Y → X` be a quasi-finite
morphism of locally Noetherian schemes and let `V = Spec B ⊆ Y` and `U = Spec A ⊆ X` be affine
opens with `f(V) ⊆ U`.  If the Dedekind different of `A → B` is defined, `1 ∈ L_{B/A}`, and the
global section `s` of `ω_{Y/X}` becomes the image `c(1)` of `1` on the chart, then the sections
over `V` of the generalized different of `s` are the Dedekind different ideal `𝔇_{B/A} ⊆ B`.

Both `𝔇_f` and the ideal sheaf associated with `𝔇_{B/A}` are coherent ideal sheaves on the
affine `V`, and a coherent sheaf on an affine scheme is the tilde of its module of sections; so
this equality of ideals of `B` is the assertion that `𝔇_f|_V = (𝔇_{B/A})~`. -/
theorem annihilatorSectionCokernel_obj_affine_eq_dedekindDifferentIdeal
    (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤)) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ (setup : DedekindDifferentSetup Γ(X, U.1) Γ(Y, V.1))
      (h1 : (1 : Γ(Y, V.1) ⊗[Γ(X, U.1)] FractionRing Γ(X, U.1)) ∈ setup.complementaryModule),
      letI : Module.Finite Γ(X, U.1) Γ(Y, V.1) := setup.finite
      selfFactorizationDualEquiv
          (ω.localEquiv U V hVU (selfFactorization Γ(X, U.1) Γ(Y, V.1))
            (restrictₗ ω.sheaf (show V.1 ≤ ⊤ from le_top) s)) =
          complementaryModuleEquivDualizingModule setup ⟨1, h1⟩ →
        (show Ideal Γ(Y, V.1) from
            (annihilatorSectionCokernel ω s).toSubmodule.obj (op V.1)) =
          dedekindDifferentIdeal setup := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  intro setup h1
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Finite Γ(X, U.1) Γ(Y, V.1) := setup.finite
  intro hs
  let φ := sectionHom ω s
  have hωq : ω.sheaf.IsQuasicoherent := ω.isQuasicoherent
  have hωc : ω.sheaf.IsCoherent := ω.isCoherent
  have hunit : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  have hunitq : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (SheafOfModules.unit Y.ringCatSheaf)).1
  have hcok : (cokernel φ).IsCoherent :=
    @_root_.SheafOfModules.cokernel_isCoherent _ _ _ _ _ hunit hωc φ
  have hD : (show Ideal Γ(Y, V.1) from
      (annihilatorSectionCokernel ω s).toSubmodule.obj (op V.1)) =
      Module.annihilator Γ(Y, V.1) Γ(cokernel φ, V.1) :=
    @annihilatorSheaf_obj_eq_annihilator Y _ (cokernel φ) hcok V
  let j := V.2.fromSpec
  let : IsOpenImmersion j := V.2.isOpenImmersion_fromSpec
  let R : CommRingCat := CommRingCat.of Γ(Y, V.1)
  let FΓ := moduleSpecΓFunctor (R := R)
  let fSpec := (Scheme.Modules.restrictFunctor j).map φ
  let OSpec := (Scheme.Modules.restrictFunctor j).obj (SheafOfModules.unit Y.ringCatSheaf)
  let MSpec := (Scheme.Modules.restrictFunctor j).obj ω.sheaf
  let : OSpec.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j _
  let : MSpec.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j _
  let F := selfFactorization Γ(X, U.1) Γ(Y, V.1)
  let eO : FΓ.obj OSpec ≃ₗ[Γ(Y, V.1)] Γ(Y, V.1) :=
    specGammaToOpenEquiv V.2 (SheafOfModules.unit Y.ringCatSheaf)
  let eM : FΓ.obj MSpec ≃ₗ[Γ(Y, V.1)] Module.Dual Γ(X, U.1) Γ(Y, V.1) :=
    ((specGammaToOpenEquiv V.2 ω.sheaf).trans (ω.localEquiv U V hVU F)).trans
      selfFactorizationDualEquiv
  let t : Module.Dual Γ(X, U.1) Γ(Y, V.1) :=
    complementaryModuleEquivDualizingModule setup ⟨1, h1⟩
  have hf : eM (FΓ.map fSpec (eO.symm 1)) = t := by
    change selfFactorizationDualEquiv
      (ω.localEquiv U V hVU F
        (specGammaToOpenEquiv V.2 ω.sheaf (FΓ.map fSpec (eO.symm 1)))) = t
    rw [specGammaToOpenEquiv_map V.2 φ (eO.symm 1)]
    have hOne : specGammaToOpenEquiv V.2 (SheafOfModules.unit Y.ringCatSheaf) (eO.symm 1) =
        (1 : Γ(Y, V.1)) := eO.apply_symm_apply 1
    rw [hOne]
    have htr : ((φ.val.app (op V.1)).hom) (1 : Γ(Y, V.1)) =
        (ω.sheaf.presheaf.map (homOfLE (show V.1 ≤ ⊤ from le_top)).op).hom s :=
      sectionHom_app_one ω s V.1
    change selfFactorizationDualEquiv
      (ω.localEquiv U V hVU F (((φ.val.app (op V.1)).hom) (1 : Γ(Y, V.1)))) = t
    rw [htr]
    exact hs
  let fΓ := FΓ.map fSpec
  let eOi := eO.toModuleIso
  let eMi := eM.toModuleIso
  have hf' : eM (fΓ.hom (eOi.symm.hom 1)) = t := hf
  let g : ModuleCat.of R R ⟶ ModuleCat.of R (Module.Dual Γ(X, U.1) Γ(Y, V.1)) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t)
  have hfg : fΓ ≫ eMi.hom = eOi.hom ≫ g := by
    apply (cancel_epi eOi.symm.hom).mp
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    apply LinearMap.ext
    intro r
    have hr : eOi.symm.hom r = r • eOi.symm.hom 1 := by
      simpa using eOi.symm.hom.hom.map_smul r (1 : Γ(Y, V.1))
    change eM (fΓ (eOi.symm.hom r)) = LinearMap.toSpanSingleton R _ t (eOi.hom (eOi.symm.hom r))
    rw [hr]
    change eM (fΓ.hom (r • eOi.symm.hom 1)) = _
    have h1' : eOi.hom (eOi.symm.hom (1 : Γ(Y, V.1))) = 1 := by simp
    calc
      _ = r • t := by rw [fΓ.hom.map_smul, eM.map_smul, hf']
      _ = LinearMap.toSpanSingleton R _ t (eOi.hom (r • eOi.symm.hom 1)) := by
        rw [eOi.hom.hom.map_smul, h1']
        simp [LinearMap.toSpanSingleton_apply]
  let cIso := cokernel.mapIso fΓ g eOi eMi hfg
  let qIso := ModuleCat.cokernelIsoRangeQuotient g
  let eC : (Scheme.Modules.restrictFunctor j).obj (cokernel φ) ≅ cokernel fSpec :=
    PreservesCokernel.iso (Scheme.Modules.restrictFunctor j) φ
  let eCSection : FΓ.obj (cokernel fSpec) ≃ₗ[Γ(Y, V.1)] Γ(cokernel φ, V.1) :=
    ((FΓ.mapIso eC.symm).toLinearEquiv).trans (specGammaToOpenEquiv V.2 (cokernel φ))
  let eQ : Γ(cokernel φ, V.1) ≃ₗ[Γ(Y, V.1)]
      (Module.Dual Γ(X, U.1) Γ(Y, V.1) ⧸ LinearMap.range (LinearMap.toSpanSingleton R _ t)) :=
    eCSection.symm.trans (specCokernelIso fSpec).toLinearEquiv |>.trans cIso.toLinearEquiv
      |>.trans qIso.toLinearEquiv
  calc
    (show Ideal Γ(Y, V.1) from
        (annihilatorSectionCokernel ω s).toSubmodule.obj (op V.1)) =
        Module.annihilator Γ(Y, V.1) Γ(cokernel φ, V.1) := hD
    _ = Module.annihilator Γ(Y, V.1)
        (Module.Dual Γ(X, U.1) Γ(Y, V.1) ⧸
          LinearMap.range (LinearMap.toSpanSingleton R _ t)) := eQ.annihilator_eq
    _ = Module.annihilator Γ(Y, V.1)
        (Module.Dual Γ(X, U.1) Γ(Y, V.1) ⧸ Submodule.span Γ(Y, V.1) {t}) := by
      rw [LinearMap.range_toSpanSingleton]
    _ = dedekindDifferentIdeal setup :=
      annihilator_dual_quotient_eq_dedekindDifferentIdeal setup h1

omit [IsLocallyNoetherian Y] in
/-- Restriction to an open containing the whole source inverts restriction from it. -/
private theorem restrictₗ_restrictₗ_top (M : Y.Modules) {V : Y.Opens}
    (htop : (⊤ : Y.Opens) ≤ V) (x : Γ(M, V)) :
    restrictₗ M (show V ≤ ⊤ from le_top) (restrictₗ M htop x) = x := by
  change (M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op)
    ((M.presheaf.map (homOfLE htop).op) x) = x
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp,
    show (homOfLE htop).op ≫ (homOfLE (show V ≤ ⊤ from le_top)).op = 𝟙 (op V) from
      Subsingleton.elim _ _, M.presheaf.map_id]
  rfl

/-- **[Stacks, Tag 0BWN], agreement of the two differents on an affine source.** When the
affine chart `V` is the whole source there is a global section of `ω_{Y/X}` whose image on the
chart is `c(1)`, and the sections over `V` of its generalized different are the Dedekind
different ideal `𝔇_{B/A}`. -/
theorem exists_sect_annihilatorSectionCokernel_obj_eq_dedekindDifferentIdeal
    (ω : RelativeDualizingModuleData f) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (htop : (⊤ : Y.Opens) ≤ V.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ (setup : DedekindDifferentSetup Γ(X, U.1) Γ(Y, V.1))
      (h1 : (1 : Γ(Y, V.1) ⊗[Γ(X, U.1)] FractionRing Γ(X, U.1)) ∈ setup.complementaryModule),
      letI : Module.Finite Γ(X, U.1) Γ(Y, V.1) := setup.finite
      ∃ s : Γ(ω.sheaf, ⊤),
        selfFactorizationDualEquiv
            (ω.localEquiv U V hVU (selfFactorization Γ(X, U.1) Γ(Y, V.1))
              (restrictₗ ω.sheaf (show V.1 ≤ ⊤ from le_top) s)) =
            complementaryModuleEquivDualizingModule setup ⟨1, h1⟩ ∧
          (show Ideal Γ(Y, V.1) from
              (annihilatorSectionCokernel ω s).toSubmodule.obj (op V.1)) =
            dedekindDifferentIdeal setup := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  intro setup h1
  let : Module.Finite Γ(X, U.1) Γ(Y, V.1) := setup.finite
  let F := selfFactorization Γ(X, U.1) Γ(Y, V.1)
  refine ⟨restrictₗ ω.sheaf htop ((ω.localEquiv U V hVU F).symm
      (selfFactorizationDualEquiv.symm
        (complementaryModuleEquivDualizingModule setup ⟨1, h1⟩))), ?hs,
    annihilatorSectionCokernel_obj_affine_eq_dedekindDifferentIdeal ω _ U V hVU setup h1 ?hs⟩
  rw [restrictₗ_restrictₗ_top ω.sheaf htop, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end Stacks.Discriminant

end
