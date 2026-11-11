module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionLocalizes
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafObjectSections

/-!
# The sections of the sheaf `Ω_{X/S}` over an affine object of `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and an object
`A = (U, T, δ)` of the small crystalline site `Cris(X/S)` with `T` affine, whose structure
morphism `T ⟶ S` factors through an affine open `V ⊆ S`.  The sheaf `Ω_{X/S}` of the chapter is
the sheaf associated with the presheaf of crystalline differentials; in the library it is
`...SmallSite.crysFormsSheaf S 1`, the sheaf associated with `⋀¹ Ω_{X/S} = Ω_{X/S}`.  This file
proves [Stacks, Tag 07J0] for it:

`Γ((U, T, δ), Ω_{X/S}) = Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ}`.

The proof is the source's: by [Stacks, Tag 07IZ] the restriction of the presheaf to `T` is the
presheaf of divided power differentials of `T`, which by [Stacks, Tag 07IY] localizes on the
basic opens of the affine scheme `T` (`...SmallSite.restrictedLocalizes_crysDifferentialForms`),
so its Zariski sheafification does not change its sections over `T`.  The restriction to `T` of the
crystalline sheafification is the Zariski sheafification of the restriction
(`...SmallSite.crysFormsSheafULiftRestrictionIso`), so the sheafification map
`...SmallSite.toCrysFormsSheaf S 1` is bijective on the sections over `A`.  The sections of the
presheaf there are `Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ}` by
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso`.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bijective_toCrysFormsSheaf_app_of_isAffine` — for every `i`, the sheafification map
  `Ω^i_{X/S} ⟶ (Ω^i_{X/S})^#` is bijective on the sections over an affine object lying over an
  affine open of the base.
* `affineCrysFormsSheafOneEquiv` — **[Stacks, Tag 07J0]**: the sections of the sheaf `Ω_{X/S}`
  over such an object are `Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ}`, linearly over `Γ(T, 𝒪_T)`.
* `affineCrysFormsSheafOneEquiv_toCrysFormsSheaf` — on the image of a section of the presheaf the
  identification is the presheaf-level one.
* `affineCrysFormsSheafOneEquiv_d` — the identification carries the image in the sheaf of the
  universal differential `d_{X/S} b` to the universal divided power differential of `b` relative
  to `Γ(V, 𝒪_V)`.

## References

* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.AffineChartLocalization

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)

/-- **The Zariski sheafification of the restriction of `Ω^i_{X/S}` to an affine ambient scheme
does not change its sections over that scheme**, for an object lying over an affine open of the
divided power base: the restriction localizes on the basic opens. -/
theorem bijective_toSheafify_formsRestrictionPresheaf_app_top
    [IsAffine A.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) (i : ℕ) :
    Function.Bijective (ConcreteCategory.hom
      ((toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          (formsRestrictionPresheaf A i)).app
        (op (⊤ : A.obj.thickening.target.scheme.Opens)))) :=
  bijective_toSheafify_app_of_isAffineOpen
    (ambientModule A (restrictedModule A (crysDifferentialForms S i)))
    (isAffineOpen_top A.obj.thickening.target.scheme) fun g _ hU hUV ↦
      (isLocalizedModule_ambientRestrictₗ_iff
        (restrictedModule A (crysDifferentialForms S i)) hUV g).1
        (restrictedLocalizes_crysDifferentialForms h hV g hU hUV)

/-- **The sheafification map `Ω^i_{X/S} ⟶ (Ω^i_{X/S})^#` is bijective on the sections over an
object of `Cris(X/S)` with affine ambient scheme lying over an affine open of the base.**  The
restriction to the ambient scheme of the crystalline sheafification is the Zariski
sheafification of the restriction, whose sections over the affine scheme are those of the
restriction. -/
theorem bijective_toCrysFormsSheaf_app_of_isAffine
    [IsAffine A.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) (i : ℕ) :
    Function.Bijective ((toCrysFormsSheaf S i).app (op A)).hom := by
  let Top : A.obj.thickening.target.scheme.Opens := ⊤
  -- the crystalline sheafification unit is bijective over `A|_T`
  have key : (toSheafify (smallTopology S) (crysDifferentialFormsULift S i).presheaf).app
          (op (A.restrictOpen Top)) ≫ (crysFormsSheafULiftRestrictionIso A i).hom.app (op Top) =
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map
          ((toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
            (formsRestrictionPresheaf A i)).app (op Top)) := by
    have := isLocallyInjective_toSheafify (crysDifferentialFormsULift S i).presheaf
    have := isLocallySurjective_toSheafify (crysDifferentialFormsULift S i).presheaf
    exact NatTrans.congr_app (CrystallineThickening.whiskerLeft_comp_restrictOpenSheafifyIso_hom A
      (toSheafify (smallTopology S) (crysDifferentialFormsULift S i).presheaf)
      (Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor
        ((presheafToSheaf _ AddCommGrpCat.{u}).obj (formsRestrictionPresheaf A i)).property)
      (crysFormsSheafULift S i).isSheaf (formsRestrictionToSheafULift A i)) (op Top)
  have h₁ : Function.Bijective (ConcreteCategory.hom
      ((toSheafify (smallTopology S) (crysDifferentialFormsULift S i).presheaf).app
        (op (A.restrictOpen Top)))) := by
    refine bijective_of_comp_right _ _ (ConcreteCategory.bijective_of_isIso
      ((crysFormsSheafULiftRestrictionIso A i).hom.app (op Top))) ?_
    rw [key]
    exact bijective_uliftFunctor_map _
      (bijective_toSheafify_formsRestrictionPresheaf_app_top A h hV i)
  -- transport to `A` itself
  have h₂ := bijective_app_of_iso _ (CrystallineThickening.isoRestrictOpenTop A) h₁
  -- and read it through `toCrysFormsSheaf`
  have h₃ : Function.Bijective (ConcreteCategory.hom
      ((Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map (toCrysFormsSheaf S i))
        AddCommGrpCat.uliftFunctor.{u + 1}).app (op A))) := by
    rw [whiskerRight_toCrysFormsSheaf]
    exact bijective_comp _ _ h₂ (ConcreteCategory.bijective_of_isIso
      (((PresheafOfModules.toPresheaf _).map (Stacks.SheafOfModules.presheafShrinkIso.{u, u + 1} _
        (crysFormsSheafULift S i).val).inv).app (op A)))
  exact (bijective_uliftFunctor_map_iff _).1 h₃

variable {A}

/-- The sections of a sheaf of `𝒪_{X/S}`-modules over an object, as a module over
`crysFormRing S A`; the sheaf's ring of scalars there is the same ring, spelled through the
structure sheaf, so the instance is supplied by name. -/
instance sheafOfModulesObjModule (F : SheafOfModules.{u} (structureSheaf S)) :
    Module (crysFormRing S A) (F.val.obj (op A)) :=
  inferInstanceAs (Module ((structureSheaf S).obj.obj (op A)) (F.val.obj (op A)))

/-- The module `Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ}` over the sections of `𝒪_{X/S}` at the object; the
two rings are the same ring `Γ(T, 𝒪_T)`, but bundled differently, so the instance is supplied by
name. -/
instance affineCrysDifferentialsObjModule {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V) :
    Module (crysFormRing S A) (affineCrysDifferentialsObj S A.obj h) :=
  inferInstanceAs (Module Γ(A.obj.thickening.target.scheme, ⊤) _)

/-- The presheaf-level identification
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso` read as a linear equivalence
over the sections of `𝒪_{X/S}`. -/
def affineCrysDifferentialsLinearEquiv [IsAffine A.obj.thickening.target.scheme]
    {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) :
    (crysDifferentials S).obj (op A) ≃ₗ[crysFormRing S A] affineCrysDifferentialsObj S A.obj h where
  toFun := (GlobalCrystallineSituation.affineCrysDifferentialsIso S A.obj h hV).hom.hom
  invFun := (GlobalCrystallineSituation.affineCrysDifferentialsIso S A.obj h hV).inv.hom
  map_add' := map_add _
  map_smul' := map_smul (GlobalCrystallineSituation.affineCrysDifferentialsIso S A.obj h hV).hom.hom
  left_inv x :=
    (GlobalCrystallineSituation.affineCrysDifferentialsIso S A.obj h hV).hom_inv_id_apply x
  right_inv x :=
    (GlobalCrystallineSituation.affineCrysDifferentialsIso S A.obj h hV).inv_hom_id_apply x

/-- **[Stacks, Tag 07J0]: the sections of the sheaf `Ω_{X/S}` over an affine object.**  For an
object `(U, T, δ)` of `Cris(X/S)` with `T` affine whose structure morphism factors through an
affine open `V ⊆ S`, the sections over `(U, T, δ)` of the sheaf `Ω_{X/S}` — the sheaf
`crysFormsSheaf S 1` associated with `⋀¹ Ω_{X/S} = Ω_{X/S}` — are the divided power differentials
`Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ}`, as modules over `Γ(T, 𝒪_T)` (the sections of `𝒪_{X/S}` there).

It is the inverse of the sheafification map on those sections
(`bijective_toCrysFormsSheaf_app_of_isAffine`), followed by `⋀¹ M = M` and the presheaf-level
identification `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso`. -/
@[stacks 07J0 "Γ((U, T, δ), Ω_{X/S}) = Ω_{Γ(T, 𝒪_T)/Γ(V, 𝒪_V), δ} for the sheaf Ω_{X/S} \
(crysFormsSheaf S 1, the sheaf associated with ⋀¹ of the crystalline differentials) on an \
affine object of Cris(X/S) mapping into an affine open V ⊆ S"]
def affineCrysFormsSheafOneEquiv [IsAffine A.obj.thickening.target.scheme]
    {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) :
    (crysFormsSheaf S 1).val.obj (op A) ≃ₗ[crysFormRing S A] affineCrysDifferentialsObj S A.obj h :=
  (LinearEquiv.ofBijective ((toCrysFormsSheaf S 1).app (op A)).hom
      (bijective_toCrysFormsSheaf_app_of_isAffine A h hV 1)).symm ≪≫ₗ
    PresheafOfModules.extPowSections 1 (crysDifferentials S) (op A) ≪≫ₗ
    exteriorPower.oneEquiv (crysFormRing S A) ((crysDifferentials S).obj (op A)) ≪≫ₗ
    affineCrysDifferentialsLinearEquiv h hV

/-- The identification `affineCrysFormsSheafOneEquiv` sends the image in the sheaf `Ω_{X/S}` of a
section `ω` of the presheaf to the image of `ω` under the presheaf-level identification
`Crystalline.GlobalCrystallineSituation.affineCrysDifferentialsIso` (after `⋀¹ M = M`). -/
theorem affineCrysFormsSheafOneEquiv_toCrysFormsSheaf [IsAffine A.obj.thickening.target.scheme]
    {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) (ω : (crysDifferentialForms S 1).obj (op A)) :
    affineCrysFormsSheafOneEquiv h hV (((toCrysFormsSheaf S 1).app (op A)).hom ω) =
      (GlobalCrystallineSituation.affineCrysDifferentialsIso S A.obj h hV).hom.hom
        (exteriorPower.oneEquiv (crysFormRing S A) ((crysDifferentials S).obj (op A))
          (PresheafOfModules.extPowSections 1 (crysDifferentials S) (op A) ω)) := by
  have he : (LinearEquiv.ofBijective ((toCrysFormsSheaf S 1).app (op A)).hom
      (bijective_toCrysFormsSheaf_app_of_isAffine A h hV 1)).symm
        (((toCrysFormsSheaf S 1).app (op A)).hom ω) = ω :=
    (LinearEquiv.ofBijective _ _).symm_apply_apply ω
  exact congrArg (fun x ↦ affineCrysDifferentialsLinearEquiv h hV
    (exteriorPower.oneEquiv (crysFormRing S A) ((crysDifferentials S).obj (op A))
      (PresheafOfModules.extPowSections 1 (crysDifferentials S) (op A) x))) he

/-- **The identification of [Stacks, Tag 07J0] is the canonical one**: it carries the image in
the sheaf `Ω_{X/S}` of the universal differential `d_{X/S} b` of a global section `b` of `𝒪_T`
to the universal divided power differential of `b` relative to `Γ(V, 𝒪_V)`. -/
theorem affineCrysFormsSheafOneEquiv_d [IsAffine A.obj.thickening.target.scheme]
    {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) (b : Γ(A.obj.thickening.target.scheme, ⊤)) :
    affineCrysFormsSheafOneEquiv h hV (((toCrysFormsSheaf S 1).app (op A)).hom
        ((PresheafOfModules.extPowSections 1 (crysDifferentials S) (op A)).symm
          ((exteriorPower.oneEquiv (crysFormRing S A) ((crysDifferentials S).obj (op A))).symm
            ((GlobalCrystallineSituation.crysDifferentialsD S A.obj).d b)))) =
      dpd (f := GlobalCrystallineSituation.affineBaseAppLE S A.obj h)
        (GlobalCrystallineSituation.crysDividedPowers S A.obj) b := by
  rw [affineCrysFormsSheafOneEquiv_toCrysFormsSheaf]
  refine (congrArg (GlobalCrystallineSituation.affineCrysDifferentialsIso S A.obj h hV).hom.hom
    ?_).trans (GlobalCrystallineSituation.affineCrysDifferentialsHom_d S A.obj h hV b)
  exact (congrArg (exteriorPower.oneEquiv (crysFormRing S A) ((crysDifferentials S).obj (op A)))
    (LinearEquiv.apply_symm_apply _ _)).trans (LinearEquiv.apply_symm_apply _ _)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
