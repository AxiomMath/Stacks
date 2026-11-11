module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingLinearDeRham07MW

/-!
# The twisted de Rham complex of a smooth lifting is the restricted de Rham complex, over `A`

In the situation of [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`), with `A = Γ(S, 𝒪_S)`,
`f : Y ⟶ S` the smooth lifting and `B = (X, Y, γ)`, part (2) of the remark builds the twisted de
Rham complex `F_Y ⊗ Ω^•_{Y/S}` of the canonical connection
(`Situation07MW.moduleWithConnection`), whose differential is, by definition, the restriction to
`Y` of the de Rham differential of [Stacks, Tag 07LM] read through
`Situation07MW.twistedFormsRestrictionIso`.  This file shows that, read as a complex of sheaves of
`A`-modules on `Y_Zar = T_Zar` (`Situation07MW.toAmbientModuleSheaf`), it is the restriction `K_T`
of the `A`-linear de Rham complex `K`
(`...CrystallineThickening.crystalDeRhamLinearAmbientComplex`).

The only point is the `A`-linearity of the identifications of the terms
(`twistedFormsRestrictionIso_hom_baseAction`), which comes down to the two images of `a ∈ A` in
`Γ(W, 𝒪_Y)` agreeing (`sectionRingEquiv_baseSection`).

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW`.

* `sectionRingEquiv_baseSection`, `twistedFormsRestrictionIso_hom_baseAction`.
* `twistedTermIso` — the `A`-linear identification of the terms.
* `twistedComplexIso` — **the twisted de Rham complex, as a complex of sheaves of `A`-modules, is
  `K_T`**, `ℕ`-indexed, and `twistedComplexExtendIso` its `ℤ`-indexed form.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)

/-- **The two images of `a ∈ A` in `Γ(W, 𝒪_Y)` agree**: the one through the object `(X, Y, γ)|_W`
of `Cris(X/S)`, read through `Γ(W, 𝒪_Y) = Γ(𝒪_{X/S}, (X, Y, γ)|_W)`, and the one through
`A ⟶ Γ(Y, f^{-1}𝒪_S) ⟶ Γ(W, f^{-1}𝒪_S) ⟶ Γ(W, 𝒪_Y)`.  Both are `f^♯(a)|_W`. -/
theorem sectionRingEquiv_baseSection (W : T.Y.Opens) (a : Γ(S.S.scheme, ⊤)) :
    (sectionRingEquiv T.crystallineThickening W
      (baseSection a (op (T.crystallineThickening.restrictOpen W))) : Γ(T.Y, W)) =
     ((inverseImageStructureMap T.toBase).hom.app (op W)).hom
       ((basePullbackRingSheaf T.toBase).obj.map (isTerminalTop.from W).op
         (baseToInverseImageRingHom T.toBase a)) := by
  have h1 : (sectionRingEquiv T.crystallineThickening W
      (baseSection a (op (T.crystallineThickening.restrictOpen W))) : Γ(T.Y, W)) =
        T.toBase.appLE ⊤ W le_top a := by
    have e1 := congrArg (fun φ => φ.hom a)
      (crysBaseAppLE_restrictOpen T.crystallineThickening.obj W)
    have e2 := congrArg (fun φ => φ.hom a)
      (Scheme.Hom.appLE_eq_app (T.crystallineThickening.restrictOpen W).obj.toBase.hom)
    have h2 : (_root_.Crystalline.openTopRes W).hom (T.toBase.appLE ⊤ W le_top a) =
        baseSection a (op (T.crystallineThickening.restrictOpen W)) := e1.trans e2
    rw [← h2]
    exact (openTopResEquiv T.crystallineThickening W).symm_apply_apply _
  rw [h1]
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat T.toBase.base
  have key : adj.unit.app S.S.scheme.sheaf ≫
      (TopCat.Sheaf.pushforward CommRingCat T.toBase.base).map
        (inverseImageStructureMap T.toBase) = ⟨T.toBase.c⟩ :=
    (Adjunction.homEquiv_unit adj _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)
  have key2 := congrArg (fun φ => (φ.hom.app (op ⊤)).hom a) key
  have hnat := ConcreteCategory.congr_hom ((inverseImageStructureMap T.toBase).hom.naturality
    (homOfLE (show W ≤ T.toBase ⁻¹ᵁ ⊤ from le_top)).op)
    ((adj.unit.app S.S.scheme.sheaf).hom.app (op ⊤) a)
  have hA : (basePullbackRingSheaf T.toBase).obj.map (isTerminalTop.from W).op
      ((basePullbackSheaf T.toBase).presheaf.map
        (homOfLE (top_le_preimage_top T.toBase)).op
        ((adj.unit.app S.S.scheme.sheaf).hom.app (op ⊤) a)) =
      (basePullbackSheaf T.toBase).presheaf.map (homOfLE (show W ≤ T.toBase ⁻¹ᵁ ⊤ from le_top)).op
        ((adj.unit.app S.S.scheme.sheaf).hom.app (op ⊤) a) := by
    change ((basePullbackSheaf T.toBase).presheaf.map _ ≫
      (basePullbackSheaf T.toBase).presheaf.map _) _ = _
    rw [← Functor.map_comp]
    rfl
  change (T.toBase.appLE ⊤ W le_top) a = (inverseImageStructureMap T.toBase).hom.app (op W)
    ((basePullbackRingSheaf T.toBase).obj.map (isTerminalTop.from W).op
      ((basePullbackSheaf T.toBase).presheaf.map (homOfLE (top_le_preimage_top T.toBase)).op
        ((adj.unit.app S.S.scheme.sheaf).hom.app (op ⊤) a)))
  rw [hA]
  refine Eq.trans ?_ hnat.symm
  exact (congrArg (fun z => T.Y.sheaf.obj.map
    (homOfLE (show W ≤ T.toBase ⁻¹ᵁ ⊤ from le_top)).op z) key2).symm

variable {F : SheafOfModules.{u} (structureSheaf S)}

/-- **The identification `(F ⊗ Ω^q_{X/S})_T ≅ F_Y ⊗ Ω^q_{Y/S}` is `A`-linear**: it intertwines
the action of `a ∈ A` on the restriction to `T` of `F ⊗ Ω^q_{X/S}` (multiplication by the image
of `a` in `𝒪_{X/S}`) with its action on `F_Y ⊗ Ω^q_{Y/S}` (multiplication by its image in
`f^{-1}𝒪_S`).  Both sheaves are generated by pure tensors `x ⊗ ω`, on which both actions
multiply `x`, by `sectionRingEquiv_baseSection`. -/
theorem twistedFormsRestrictionIso_hom_baseAction (q : ℕ) (a : Γ(S.S.scheme, ⊤)) :
    Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor T.crystallineThickening).op
        (tensorFormsBaseAction F q a).asHom.hom ≫ (T.twistedFormsRestrictionIso F q).hom =
      (T.twistedFormsRestrictionIso F q).hom ≫
        (T.twistedBaseAction (twistedTerm T.toBase (T.liftingModule F) q) a).asHom.hom := by
  have := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F q)
  have := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F q)
  refine CrystallineThickening.restrictOpenSheafify_hom_ext T.crystallineThickening
    (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F q))
    (isSheaf_ambientTensorSheafULift F _) ?_
  have h1 : Functor.whiskerLeft
      (CrystallineThickening.restrictOpenFunctor T.crystallineThickening).op
      (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F q)) ≫
        (T.twistedFormsRestrictionIso F q).hom =
          tensorFormsAmbientUnitULift F (T.formsComparison q) :=
    CrystallineThickening.whiskerLeft_comp_restrictOpenSheafifyIso_hom T.crystallineThickening
      (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F q))
      (isSheaf_ambientTensorSheafULift F _) (tensorDifferentialFormsSheaf F q).property
      (tensorFormsAmbientUnitULift F (T.formsComparison q))
  have e2 := congrArg (Functor.whiskerLeft
    (CrystallineThickening.restrictOpenFunctor T.crystallineThickening).op)
    (toSheafify_tensorFormsBaseAction F q a)
  have key3 : Functor.whiskerLeft
      (CrystallineThickening.restrictOpenFunctor T.crystallineThickening).op
        (presheafBaseAction _ a).asHom ≫ tensorFormsAmbientUnitULift F (T.formsComparison q) =
      tensorFormsAmbientUnitULift F (T.formsComparison q) ≫
        (T.twistedBaseAction (twistedTerm T.toBase (T.liftingModule F) q) a).asHom.hom := by
    refine NatTrans.ext (funext fun V => AddCommGrpCat.ext fun p => ?_)
    obtain ⟨t⟩ := p
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add t t' ht ht' =>
      exact (map_add _ (ULift.up t) (ULift.up t')).trans
        ((congrArg₂ (· + ·) ht ht').trans (map_add _ (ULift.up t) (ULift.up t')).symm)
    | tmul x ω =>
      refine ULift.ext ?_
      change Stacks.PullbackTensorCoherence.tmul
          T.crystallineThickening.obj.thickening.target.scheme.toRingedSpace
          (crysAmbientSchemeModules F T.crystallineThickening)
          (relativeDifferentialForms T.toBase (q : ℤ)) V
          (baseSection a (op (T.crystallineThickening.restrictOpen V.unop)) •
            (show (F.val : PresheafOfModules.{u}
                (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)).obj
              (op (T.crystallineThickening.restrictOpen V.unop)) from x))
          ((T.formsComparison q).toFun V.unop ω) =
        (show (Stacks.RingedSpace.structureRingSheaf
            T.crystallineThickening.obj.thickening.target.scheme.toRingedSpace).obj.obj V from
          ((inverseImageStructureMap T.toBase).hom.app V).hom
            ((basePullbackRingSheaf T.toBase).obj.map (isTerminalTop.from V.unop).op
              (baseToInverseImageRingHom T.toBase a))) •
          Stacks.PullbackTensorCoherence.tmul
            T.crystallineThickening.obj.thickening.target.scheme.toRingedSpace
            (crysAmbientSchemeModules F T.crystallineThickening)
            (relativeDifferentialForms T.toBase (q : ℤ)) V x ((T.formsComparison q).toFun V.unop ω)
      have e3 := crysAmbient_smul F T.crystallineThickening V.unop
        (baseSection a (op (T.crystallineThickening.restrictOpen V.unop))) x
      have e4 := T.sectionRingEquiv_baseSection V.unop a
      exact (congrArg (fun z => Stacks.PullbackTensorCoherence.tmul
          T.crystallineThickening.obj.thickening.target.scheme.toRingedSpace
          (crysAmbientSchemeModules F T.crystallineThickening)
          (relativeDifferentialForms T.toBase (q : ℤ)) V z ((T.formsComparison q).toFun V.unop ω))
          e3).trans ((congrArg (fun r => Stacks.PullbackTensorCoherence.tmul
          T.crystallineThickening.obj.thickening.target.scheme.toRingedSpace
          (crysAmbientSchemeModules F T.crystallineThickening)
          (relativeDifferentialForms T.toBase (q : ℤ)) V
          (r • (show (crysAmbientSchemeModules F T.crystallineThickening).val.obj V from x))
          ((T.formsComparison q).toFun V.unop ω))
          e4).trans (Stacks.PullbackTensorCoherence.tmul_smul_left _ _ _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    ((Functor.whiskerLeft_comp _ _ _).symm.trans
    (e2.trans (Functor.whiskerLeft_comp _ _ _)))).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h1).trans (key3.trans ((reassoc_of% h1) _).symm))))

variable (hF : F.IsQuasicoherentOnSite)

/-- The `A`-linear morphism `(F ⊗ Ω^q_{X/S})_T ⟶ F_Y ⊗ Ω^q_{Y/S}` underlying
`twistedFormsRestrictionIso`. -/
def twistedTermHom (q : ℕ) :
    (CrystallineThickening.linearAmbientRestriction T.crystallineThickening).obj
        (linearTensorFormsSheaf F q) ⟶
      T.toAmbientModuleSheaf.obj ((T.moduleWithConnection hF).complex.X q) :=
  ObjectProperty.homMk (Stacks.ModuleCatLift.ofEndActionMap Γ(S.S.scheme, ⊤) _ _
    (T.twistedFormsRestrictionIso F q).hom
    (fun a => T.twistedFormsRestrictionIso_hom_baseAction q a))

/-- The abelian sheaf morphism underlying `twistedTermHom` is invertible. -/
instance isIso_ambientForget_map_twistedTermHom (q : ℕ) :
    IsIso ((CrystallineThickening.ambientForget T.crystallineThickening).map
      (T.twistedTermHom hF q)) :=
  ⟨⟨ObjectProperty.homMk (T.twistedFormsRestrictionIso F q).inv,
    ObjectProperty.hom_ext _ (T.twistedFormsRestrictionIso F q).hom_inv_id,
    ObjectProperty.hom_ext _ (T.twistedFormsRestrictionIso F q).inv_hom_id⟩⟩

/-- `twistedTermHom` is invertible. -/
instance isIso_twistedTermHom (q : ℕ) : IsIso (T.twistedTermHom hF q) :=
  isIso_of_reflects_iso _ (CrystallineThickening.ambientForget T.crystallineThickening)

/-- **The `A`-linear identification of the terms**:
`F_Y ⊗ Ω^q_{Y/S}`, read as a sheaf of `A`-modules, is the restriction to `T` of `F ⊗ Ω^q_{X/S}`
read as a sheaf of `A`-modules. -/
def twistedTermIso (q : ℕ) :
    T.toAmbientModuleSheaf.obj ((T.moduleWithConnection hF).complex.X q) ≅
      (CrystallineThickening.linearAmbientRestriction T.crystallineThickening).obj
        (linearTensorFormsSheaf F q) :=
  (@asIso _ _ _ _ (T.twistedTermHom hF q) (T.isIso_twistedTermHom hF q)).symm

/-- The restricted de Rham differential, read through `twistedFormsRestrictionIso`, is the twisted
differential: this is the definition of the latter. -/
theorem whiskerLeft_crystalDeRhamDifferential_comp_twistedFormsRestrictionIso_hom (i : ℕ) :
    Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor T.crystallineThickening).op
        (crystalDeRhamDifferential hF i).hom ≫ (T.twistedFormsRestrictionIso F (i + 1)).hom =
      (T.twistedFormsRestrictionIso F i).hom ≫ T.twistedDifferentialULift hF i :=
  (Iso.hom_inv_id_assoc _ _).symm

/-- **The twisted de Rham complex `F_Y ⊗ Ω^•_{Y/S}`, read as a complex of sheaves of `A`-modules,
is the restriction `K_T` of the `A`-linear de Rham complex**, `ℕ`-indexed; in each degree the
identification is `twistedTermIso`, and the differentials match because the twisted differential
is, by definition, the restricted de Rham differential. -/
def twistedComplexIso :
    ((CrystallineThickening.linearAmbientRestriction T.crystallineThickening).mapHomologicalComplex
        _).obj (crystalDeRhamLinearNatComplex hF) ≅
      (T.toAmbientModuleSheaf.mapHomologicalComplex _).obj (T.moduleWithConnection hF).complex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => @asIso _ _ _ _ (T.twistedTermHom hF q) (T.isIso_twistedTermHom hF q)) (by
    rintro i j (rfl : i + 1 = j)
    simp only [Functor.mapHomologicalComplex_obj_d, ModuleWithConnection.complex_d,
      crystalDeRhamLinearNatComplex, CochainComplex.of_d, asIso_hom]
    refine (CrystallineThickening.ambientForget T.crystallineThickening).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    refine ObjectProperty.hom_ext _ ?_
    exact (T.whiskerLeft_crystalDeRhamDifferential_comp_twistedFormsRestrictionIso_hom hF i).symm)

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

end

end
