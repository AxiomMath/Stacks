module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantCoefficientsEquivalence
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocallyConstantAdicDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedChangeOfRings
public import StacksFrontier.Deformation.ToposThickening.DerivedComplexLift
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.CanonicalSheafCertificate

/-!
# Derived reduction of pro-étale complexes computed by K-flat representatives

Let `X` be a scheme, `Λ` a ring and `𝔞 ⊆ Λ` an ideal. The derived reduction `K ⊗_Λ^L Λ/𝔞` of an
object `K` of `D(X_proét, Λ)` is any derived base change along reduction modulo `𝔞` of the
constant coefficient ring sheaves, in the sense of Stacks 0DIZ: a left derived functor of
degreewise extension of scalars. This file shows that every such derived base change is computed
by K-flat representatives: read in the derived category of sheaves of `Λ/𝔞`-modules through the
constant coefficients equivalence, it is the derived extension of scalars
`Stacks.ModuleSheaf.derivedExtendScalars` along `Λ → Λ/𝔞`, which is constructed by descending
degreewise extension of scalars from the K-flat complexes.

## Main definitions

* `AlgebraicGeometry.ProEtale.constantCoefficientExtendScalars`: extension of scalars along
  reduction modulo `𝔞` of sheaves of modules over the constant coefficient ring sheaves.
* `AlgebraicGeometry.ProEtale.restrictScalarsCompToCoefficientModuleSheafIso` and
  `AlgebraicGeometry.ProEtale.extendScalarsCompToCoefficientModuleSheafIso`: restriction and
  extension of scalars commute with the constant coefficients equivalence.
* `AlgebraicGeometry.ProEtale.IsKFlatCoefficientComplex`: a complex whose reading as a complex of
  sheaves of `Λ`-modules is K-flat.

## Main results

* `CategoryTheory.LeftDerivedByResolutions.isIso_comparison_app_of_resolving`: the comparison of
  a left derived functor of a degreewise functor is invertible on a resolving class on which the
  degreewise functor preserves quasi-isomorphisms.
* `AlgebraicGeometry.ProEtale.isIso_comparison_app_of_isKFlatCoefficientComplex`: the comparison
  of a derived reduction is invertible at a K-flat representative.
* `AlgebraicGeometry.ProEtale.nonempty_derivedCoefficientModuleSheafEquivalence_baseChange_iso`:
  every derived reduction is the derived extension of scalars of sheaves of `Λ`-modules.

## Implementation notes

The coefficient ring lies in the universe `max (u + 1) w` of the module sections, which is the
universe in which the derived extension of scalars of sheaves of modules is constructed.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory.LeftDerivedByResolutions

variable {A A' : Type*} [Category A] [Abelian A] [Category A'] [Abelian A']
  [HasDerivedCategory A] [HasDerivedCategory A'] (F : A ⥤ A') [F.Additive]

/-- **A left derived functor of a degreewise functor is computed by a resolving class.** Let
`F : A ⥤ A'` be additive and `P` a class of complexes such that every complex receives a
quasi-isomorphism from a member of `P`, and such that `F`, applied degreewise, carries
quasi-isomorphisms between members of `P` to quasi-isomorphisms. Then for every left derived
functor `G` of `F` with comparison `β`, the comparison is invertible at every member of `P`. -/
theorem isIso_comparison_app_of_resolving (P : CochainComplex A ℤ → Prop)
    (hP : ∀ K : CochainComplex A ℤ, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), P L ∧ QuasiIso p)
    (hF : ∀ {L L' : CochainComplex A ℤ} (f : L ⟶ L'), P L → P L' → QuasiIso f →
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
    (G : DerivedCategory A ⥤ DerivedCategory A')
    (β : DerivedCategory.Q ⋙ G ⟶ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hG : G.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
    (K : CochainComplex A ℤ) (hK : P K) : IsIso (β.app K) := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let PH : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) := fun X => P X.as
  have hres : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (Y : HomotopyCategory A (ComplexShape.up ℤ)) (_ : PH Y) (s : Y ⟶ X), W s := by
    intro X
    obtain ⟨L, p, hL, hp⟩ := hP X.as
    exact ⟨(HomotopyCategory.quotient _ _).obj L, hL, (HomotopyCategory.quotient _ _).map p,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 hp)⟩
  let Uh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have hUh : ∀ {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (s : X ⟶ Y), W s → PH X →
      PH Y → IsIso (Uh.map s) := by
    intro X Y s hs hX hY
    obtain ⟨g, hg⟩ := (HomotopyCategory.quotient _ _).map_surjective s
    have hg' : QuasiIso g := by
      rwa [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
        hg]
    have key : IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory _).map
        ((HomotopyCategory.quotient _ _).map g))) := by
      rw [Functor.mapHomotopyCategory_map]
      exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
          ((HomologicalComplex.mem_quasiIso_iff _).2 (hF g hX hY hg')))
    show IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory _).map s))
    exact hg ▸ key
  have := hasPointwiseLeftDerivedFunctor_of_resolutions W PH hres Uh hUh
  let Gt := Uh.totalLeftDerived DerivedCategory.Qh W
  let α := Uh.totalLeftDerivedCounit DerivedCategory.Qh W
  let e : HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ Uh ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso A')
  let β₀ :
      DerivedCategory.Q ⋙ Gt ⟶ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv Gt ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ _) α ≫ e.hom
  have hβ₀ : ∀ L : CochainComplex A ℤ, P L → IsIso (β₀.app L) := by
    intro L hL
    have := isIso_app_of_resolutions W PH hres Uh hUh DerivedCategory.Qh Gt α
      ((HomotopyCategory.quotient _ _).obj L) hL
    dsimp [β₀]
    infer_instance
  have := isLeftDerivedFunctor_of_isIso_on_resolvingComplexes P hres
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) Uh e Gt β₀ hβ₀
  let i := Functor.leftDerivedUnique G Gt β₀ β (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  have hi : Functor.whiskerLeft DerivedCategory.Q i.hom ≫ β = β₀ := by
    simp [i, Functor.leftDerivedUnique]
  have heq : i.hom.app (DerivedCategory.Q.obj K) ≫ β.app K = β₀.app K :=
    NatTrans.congr_app hi K
  rw [← isIso_comp_left_iff (i.hom.app (DerivedCategory.Q.obj K)), heq]
  exact hβ₀ K hK

end CategoryTheory.LeftDerivedByResolutions

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.hasSheafify_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (𝔞 : Ideal Λ)

/-- Reduction modulo `𝔞` carries the image of a coefficient in the sections of the constant
coefficient ring sheaf over an object `U` to the image of its residue class. -/
theorem constantCoefficientRingReduction_app_toCoefficientSections (U : X.ProEtᵒᵖ) (c : Λ) :
    ((constantCoefficientRingReduction.{u, max (u + 1) w, w} X Λ 𝔞).hom.app U).hom
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O).obj.map
          ((terminalIsTerminal (C := X.ProEt)).op.to U)).hom
            (toCoefficientSections.{u, max (u + 1) w, w} X Λ c)) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).O).obj.map
          ((terminalIsTerminal (C := X.ProEt)).op.to U)).hom
        (toCoefficientSections.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞) (Ideal.Quotient.mk 𝔞 c)) := by
  have h1 := ConcreteCategory.congr_hom
    ((constantCoefficientRingReduction.{u, max (u + 1) w, w} X Λ 𝔞).hom.naturality
      ((terminalIsTerminal (C := X.ProEt)).op.to U))
    (toCoefficientSections.{u, max (u + 1) w, w} X Λ c)
  have h2 := toSheafify_naturality (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv.{max (u + 1) w, max (u + 1) w} (R := Λ ⧸ 𝔞)).symm.toRingHom.comp
        ((Ideal.Quotient.mk 𝔞).comp
          (ULift.ringEquiv.{max (u + 1) w, max (u + 1) w} (R := Λ)).toRingHom))))
  have h3 : ((constantCoefficientRingReduction.{u, max (u + 1) w, w} X Λ 𝔞).hom.app
      (op (⊤_ X.ProEt))).hom (toCoefficientSections.{u, max (u + 1) w, w} X Λ c) =
      toCoefficientSections.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞) (Ideal.Quotient.mk 𝔞 c) :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app h2 (op (⊤_ X.ProEt))) (ULift.up c)).symm
  exact h1.trans (congrArg (fun y => ((Stacks.SheafOfModules.Tensor.ringSheaf
    (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).O).obj.map
      ((terminalIsTerminal (C := X.ProEt)).op.to U)).hom y) h3)

/-- Reading a sheaf of modules over the constant coefficient ring sheaf of `Λ/𝔞` as a sheaf of
modules over that of `Λ` and then as a sheaf of `Λ`-modules is reading it as a sheaf of
`Λ/𝔞`-modules and restricting scalars along `Λ → Λ/𝔞`: both are the same sections, and the two
actions of `Λ` agree by
`AlgebraicGeometry.ProEtale.constantCoefficientRingReduction_app_toCoefficientSections`. -/
def restrictScalarsCompToCoefficientModuleSheafIso :
    SheafOfModules.restrictScalars (constantCoefficientRingReduction.{u, max (u + 1) w, w} X Λ 𝔞) ⋙
        toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ ≅
      toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞) ⋙
        Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk 𝔞) :=
  NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (NatIso.ofComponents (fun U =>
    { hom := ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars
          (constantCoefficientRingReduction.{u, max (u + 1) w, w} X Λ 𝔞) ⋙
            toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ).obj M).obj.obj U)
        (Y := ((toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞) ⋙
          Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk 𝔞)).obj M).obj.obj U)
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun c x => congrArg
            (fun y : ((Stacks.SheafOfModules.Tensor.ringSheaf
              (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).O).obj.obj U) =>
                y • id (α := M.val.obj U) x)
            (constantCoefficientRingReduction_app_toCoefficientSections X Λ 𝔞 U c) }
      inv := ModuleCat.ofHom
        (X := ((toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞) ⋙
          Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk 𝔞)).obj M).obj.obj U)
        (Y := ((SheafOfModules.restrictScalars
          (constantCoefficientRingReduction.{u, max (u + 1) w, w} X Λ 𝔞) ⋙
            toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ).obj M).obj.obj U)
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun c x => congrArg
            (fun y : ((Stacks.SheafOfModules.Tensor.ringSheaf
              (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).O).obj.obj U) =>
                y • id (α := M.val.obj U) x)
            (constantCoefficientRingReduction_app_toCoefficientSections X Λ 𝔞 U c).symm }
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => rfl))) (fun _ => rfl)

/-- Extension of scalars along reduction modulo `𝔞` of sheaves of modules over the constant
coefficient ring sheaves: the functor whose degreewise application is
`Deformation.ComplexLift.extensionOfScalarsCochainComplex`. -/
abbrev constantCoefficientExtendScalars :
    RingedSite.Modules.{u + 1, u, max (u + 1) w}
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ) ⥤
      RingedSite.Modules.{u + 1, u, max (u + 1) w}
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)) :=
  Stacks.Sheaves.RingedToposModules.extendScalars (Scheme.ProEt.topology X)
    (constantCoefficientReduction.{u, max (u + 1) w, w} X Λ 𝔞).hom
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).O).property

/-- Extension of scalars along reduction modulo `𝔞` is additive, being a left adjoint. -/
instance constantCoefficientExtendScalars_additive :
    (constantCoefficientExtendScalars.{u, w} X Λ 𝔞).Additive :=
  (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction (Scheme.ProEt.topology X)
    (constantCoefficientReduction.{u, max (u + 1) w, w} X Λ 𝔞).hom
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).O).property)
    |>.left_adjoint_additive

/-- The composite of extension of scalars with the reading as sheaves of `Λ/𝔞`-modules is
additive. -/
instance constantCoefficientExtendScalars_comp_toCoefficientModuleSheaf_additive :
    (constantCoefficientExtendScalars.{u, w} X Λ 𝔞 ⋙
      toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).Additive :=
  inferInstance

/-- **Extension of scalars commutes with the constant coefficients equivalence.** Extension of
scalars along reduction modulo `𝔞` of sheaves of modules over the constant coefficient ring
sheaves, read as sheaves of `Λ/𝔞`-modules, is extension of scalars along `Λ → Λ/𝔞` of sheaves
of `Λ`-modules: both are left adjoint to restriction of scalars, and the two restrictions of
scalars correspond by
`AlgebraicGeometry.ProEtale.restrictScalarsCompToCoefficientModuleSheafIso`. -/
def extendScalarsCompToCoefficientModuleSheafIso :
    constantCoefficientExtendScalars.{u, w} X Λ 𝔞 ⋙
        toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞) ≅
      toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ ⋙
        Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk 𝔞) :=
  let ea := (toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ).asEquivalence
  let eb := (toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).asEquivalence
  let ρ : eb.inverse ⋙ SheafOfModules.restrictScalars
        (constantCoefficientRingReduction.{u, max (u + 1) w, w} X Λ 𝔞) ≅
      Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk 𝔞) ⋙
        ea.inverse :=
    Iso.isoCompInverse (H := ea)
      (Functor.isoWhiskerLeft eb.inverse (restrictScalarsCompToCoefficientModuleSheafIso X Λ 𝔞) ≪≫
        (Functor.isoWhiskerRight eb.counitIso
          (Stacks.ModuleSheaf.restrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk 𝔞)) :
            (eb.inverse ⋙ eb.functor) ⋙ Stacks.ModuleSheaf.restrictScalars
              (Scheme.ProEt.topology X) (Ideal.Quotient.mk 𝔞) ≅ _) ≪≫ Functor.leftUnitor _)
  Adjunction.leftAdjointUniq
    ((Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction (Scheme.ProEt.topology X)
      (constantCoefficientReduction.{u, max (u + 1) w, w} X Λ 𝔞).hom
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O).property
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).O).property).comp
      eb.toAdjunction)
    ((ea.toAdjunction.comp (Stacks.ModuleSheaf.extendRestrictScalarsAdj (Scheme.ProEt.topology X)
      (Ideal.Quotient.mk 𝔞))).ofNatIsoRight ρ.symm)

section Comparison

attribute [local instance] Sheaf.monoidalCategory

/-- Extension of scalars along reduction modulo `𝔞` of complexes of sheaves of modules over the
constant coefficient ring sheaves, read as complexes of sheaves of `Λ/𝔞`-modules, is degreewise
extension of scalars along `Λ → Λ/𝔞` of complexes of sheaves of `Λ`-modules. -/
def extensionOfScalarsCochainComplexCompIso :
    (constantCoefficientExtendScalars.{u, w} X Λ 𝔞).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
          (Ideal.Quotient.mk 𝔞)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (extendScalarsCompToCoefficientModuleSheafIso X Λ 𝔞)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- A complex of sheaves of modules over the constant coefficient ring sheaf whose reading as a
complex of sheaves of `Λ`-modules is K-flat. -/
abbrev IsKFlatCoefficientComplex (L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)) ℤ) : Prop :=
  CochainComplex.KFlatBifunctor.KFlat
    (MonoidalCategory.curriedTensor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (((toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L)

/-- Every complex of sheaves of modules over the constant coefficient ring sheaf receives a
quasi-isomorphism from one whose reading as a complex of sheaves of `Λ`-modules is K-flat. -/
theorem exists_quasiIso_isKFlatCoefficientComplex
    (K₀ : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)) ℤ) :
    ∃ (L : CochainComplex _ ℤ) (p : L ⟶ K₀), IsKFlatCoefficientComplex X Λ L ∧ QuasiIso p := by
  let a := toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ
  let aC := a.mapHomologicalComplex (ComplexShape.up ℤ)
  have : aC.IsEquivalence := isEquivalence_mapHomologicalComplex_toCoefficientModuleSheaf X Λ
  obtain ⟨M, m, hM, hm⟩ := Stacks.ModuleSheaf.exists_kFlat_quasiIso (aC.obj K₀)
  let ε : aC.obj (aC.asEquivalence.inverse.obj M) ≅ M := aC.asEquivalence.counitIso.app M
  refine ⟨aC.asEquivalence.inverse.obj M, aC.preimage (ε.hom ≫ m),
    CochainComplex.KFlatBifunctor.KFlat.of_iso _ hM ε.symm, ?_⟩
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ a]
  show QuasiIso (aC.map (aC.preimage (ε.hom ≫ m)))
  rw [Functor.map_preimage]
  infer_instance

/-- Degreewise extension of scalars along reduction modulo `𝔞` carries quasi-isomorphisms between
complexes whose readings as complexes of sheaves of `Λ`-modules are K-flat to
quasi-isomorphisms. -/
theorem quasiIso_extendScalars_map_of_isKFlatCoefficientComplex
    {L L' : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)) ℤ} (f : L ⟶ L')
    (hL : IsKFlatCoefficientComplex X Λ L) (hL' : IsKFlatCoefficientComplex X Λ L')
    (hf : QuasiIso f) :
    QuasiIso (((constantCoefficientExtendScalars.{u, w} X Λ 𝔞).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞))]
  refine (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (extensionOfScalarsCochainComplexCompIso X Λ 𝔞) f)).2 ?_
  exact Stacks.ModuleSheaf.quasiIso_extendScalars_map_of_kFlat (Scheme.ProEt.topology X) _
    (((toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) hL hL' inferInstance

/-- **The comparison of a derived reduction is invertible at a K-flat representative.** -/
theorem isIso_comparison_app_of_isKFlatCoefficientComplex
    (T : DerivedReduction.{u, max (u + 1) w, w} X Λ 𝔞)
    (L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)) ℤ)
    (hL : IsKFlatCoefficientComplex X Λ L) : IsIso (T.comparison.app L) :=
  LeftDerivedByResolutions.isIso_comparison_app_of_resolving
    (constantCoefficientExtendScalars.{u, w} X Λ 𝔞) (IsKFlatCoefficientComplex X Λ)
    (exists_quasiIso_isKFlatCoefficientComplex X Λ)
    (quasiIso_extendScalars_map_of_isKFlatCoefficientComplex X Λ 𝔞)
    T.baseChange T.comparison T.isLeftDerived L hL

/-- **Every derived reduction is computed by K-flat representatives.** For any derived base change
`T` along reduction modulo `𝔞` of the constant coefficient ring sheaves (Stacks 0DIZ) and any
object `K` of `D(X_proét, Λ)`, the derived reduction `T(K)`, read as an object of the derived
category of sheaves of `Λ/𝔞`-modules, is the derived extension of scalars `K ⊗_Λ^L Λ/𝔞` of `K`
read as an object of the derived category of sheaves of `Λ`-modules.

Both are left derived functors of degreewise extension of scalars, which correspond under the
constant coefficients equivalence; the comparison of `T` is invertible at every complex whose
reading as a complex of sheaves of `Λ`-modules is K-flat, and such complexes resolve every
complex. -/
theorem nonempty_derivedCoefficientModuleSheafEquivalence_baseChange_iso
    (T : DerivedReduction.{u, max (u + 1) w, w} X Λ 𝔞)
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ) :
    Nonempty ((derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)).functor.obj
        (T.baseChange.obj K) ≅
      (Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X)
        (Ideal.Quotient.mk 𝔞)).obj
          ((derivedCoefficientModuleSheafEquivalence.{u, max (u + 1) w, w} X Λ).functor.obj
            K)) := by
  let a := toCoefficientModuleSheaf.{u, max (u + 1) w, w} X Λ
  let b := toCoefficientModuleSheaf.{u, max (u + 1) w, w} X (Λ ⧸ 𝔞)
  obtain ⟨L, p, hL, hp⟩ := exists_quasiIso_isKFlatCoefficientComplex X Λ
    (DerivedCategory.Q.objPreimage K)
  have := isIso_comparison_app_of_isKFlatCoefficientComplex X Λ 𝔞 T L hL
  let eK : DerivedCategory.Q.obj L ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  exact ⟨b.mapDerivedCategory.mapIso (T.baseChange.mapIso eK.symm ≪≫ asIso (T.comparison.app L)) ≪≫
    b.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((extensionOfScalarsCochainComplexCompIso X Λ 𝔞).app L) ≪≫
    (Stacks.ModuleSheaf.derivedExtendScalarsObjIso (Scheme.ProEt.topology X)
      (Ideal.Quotient.mk 𝔞) hL).symm ≪≫
    (Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X)
      (Ideal.Quotient.mk 𝔞)).mapIso
      ((a.mapDerivedCategoryFactors.app L).symm ≪≫ a.mapDerivedCategory.mapIso eK)⟩

end Comparison

end AlgebraicGeometry.ProEtale

end
