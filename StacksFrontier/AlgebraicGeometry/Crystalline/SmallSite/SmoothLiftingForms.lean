module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmoothLiftingDifferentials
public import StacksFrontier.AlgebraicGeometry.DeRham.TwistedFormsSections
public import StacksFrontier.LinearAlgebra.TensorAlgebra.PowMapBijective
public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.AffineOpenWedge
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTensorFormsAmbient

/-!
# Differential forms of a smooth lifting, read on `Cris(X/S)`

In the situation of Remark [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`: `S = Spec A` affine,
`p` nilpotent in `A`, `Y ⟶ S` smooth and `X = Y ×_S S₀`), the smooth lifting `Y` is the ambient
scheme of the object `A = (X, Y, γ)` of `Cris(X/S)` of part (1) of the remark.  This file compares
the crystalline differential forms `Ω^q_{X/S}` over the restrictions `A|_W` with the relative
differential forms `Ω^q_{Y/S}` of `Y ⟶ S`:

* the divided power relations vanish on `Y` (`Crystalline.GlobalCrystallineSituation
  .isIso_smoothLifting_toDpDifferentials`), so `Ω_{Y/S} ≅ Ω_{Y/S,δ}` (`relativeDifferentialsIsoDp`);
* composing with [Stacks, Tag 07IZ] on sections gives `Ω_{X/S}(A|_W) ⟶ Ω_{Y/S}(W)`
  (`formsCompOneRel`), and its exterior power followed by the wedge of generators gives
  `Ω^q_{X/S}(A|_W) ⟶ Ω^q_{Y/S}(W)` (`formsCompRel`);
* this is a `...SmallSite.FormsComparison` (`formsComparison`): semilinear, natural, and bijective
  over affine opens lying over affine opens of the base (by `Stacks.AffineExteriorPower
  .affineOpenExteriorPowerΓIso`).

## Main results

* `formsCompOneRel_crysD` — the crystalline differential `d b` goes to the universal relative
  derivation `d b` of `Y/S`.
* `formsCompRel_ιMulti`, `formsCompRel_leftWedge` — the comparison is multiplicative: it carries the
  crystalline wedge `α ∧ ω` to the relative exterior product.
* `formsCompRel_deRham` — **the comparison intertwines the de Rham differential of
  [Stacks, Tag 07J4] with the relative de Rham differential of `Y/S`.**
* `bijective_formsCompRel` and `formsComparison`.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
-/

@[expose] public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Hom

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)

/-- The comparison map `Ω_{Y/S} ⟶ Ω_{Y/S,δ}` is an isomorphism on the smooth lifting. -/
theorem isIso_toDpDifferentials :
    IsIso (toDpDifferentials T.crystallineThickening.obj.thickening.target S.S.scheme
      T.crystallineThickening.obj.toBase.hom) := by
  have h1 := T.isAffine
  have h2 := T.isSmooth
  exact @isIso_smoothLifting_toDpDifferentials S h1 T.prime_nilpotent T.Y T.toBase h2 T.toY
    T.cartesian

/-- `Ω_{Y/S} ≅ Ω_{Y/S,δ}`. -/
def relativeDifferentialsIsoDp : relativeDifferentials T.toBase ≅
    dpDifferentialsSheaf T.crystallineThickening.obj.thickening.target S.S.scheme
      T.crystallineThickening.obj.toBase.hom :=
  @asIso _ _ _ _ (toDpDifferentials T.crystallineThickening.obj.thickening.target S.S.scheme
    T.crystallineThickening.obj.toBase.hom) T.isIso_toDpDifferentials

attribute [local instance] commRingRingCatSheafSections

/-- The identification of the ring of sections of `𝒪_{X/S}` over `A|_W` with `Γ(Y, W)`. -/
def sectionRingIso (W : T.Y.Opens) :
    crysFormRing S (T.crystallineThickening.restrictOpen W) ≃+* ↑(T.Y.ringCatSheaf.obj.obj (op W))
        :=
  sectionRingEquiv T.crystallineThickening W

/-- **`Ω_{X/S}(A|_W) ⟶ Ω_{Y/S}(W)`**: [Stacks, Tag 07IZ] on sections, followed by the inverse of
`Ω_{Y/S} ≅ Ω_{Y/S,δ}`. -/
def formsCompOneRel (W : T.Y.Opens) :
    (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)) →+
      (relativeDifferentials T.toBase).val.obj (op W) :=
  ((T.relativeDifferentialsIsoDp.inv.val.app (op W)).hom.toAddMonoidHom).comp
    ((restrictedToSheaf T.crystallineThickening.obj).app (op W)).hom.toAddMonoidHom

/-- `formsCompOneRel` is semilinear over `sectionRingIso`. -/
theorem formsCompOneRel_smul (W : T.Y.Opens) (r : crysFormRing S
    (T.crystallineThickening.restrictOpen W))
    (x : (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.formsCompOneRel W (r • x) = T.sectionRingIso W r • T.formsCompOneRel W x := by
  have h2 : r • x = (show (restrictedCrysDifferentials S T.crystallineThickening.obj).obj (op W)
      from
      (sectionRingEquiv T.crystallineThickening W r) •
        (show (restrictedCrysDifferentials S T.crystallineThickening.obj).obj (op W) from x)) :=
    congrArg (fun c : crysFormRing S (T.crystallineThickening.restrictOpen W) ↦ c • x)
      (restrictOpenRingHom_sectionRingEquiv T.crystallineThickening W r).symm
  exact (congrArg (T.formsCompOneRel W) h2).trans
    ((congrArg (T.relativeDifferentialsIsoDp.inv.val.app (op W)).hom
      (((restrictedToSheaf T.crystallineThickening.obj).app (op W)).hom.map_smul _ _)).trans
      ((T.relativeDifferentialsIsoDp.inv.val.app (op W)).hom.map_smul _ _))

/-- `formsCompOneRel` as a semilinear map over `sectionRingIso`. -/
def formsCompOneRelₛₗ (W : T.Y.Opens) :
    (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)) →ₛₗ[
      (T.sectionRingIso W).toRingHom] (relativeDifferentials T.toBase).val.obj (op W) where
  toFun := T.formsCompOneRel W
  map_add' := (T.formsCompOneRel W).map_add
  map_smul' := T.formsCompOneRel_smul W


/-- The wedge comparison `⋀^q_{Γ(Y, W)} Ω_{Y/S}(W) ⟶ Ω^q_{Y/S}(W)`. -/
abbrev formsExtCmp (q : ℕ) (W : T.Y.Opens) :=
  (deRhamAlgebras T.toBase).exterior.toPresheafGradedAlgebra.extCmpSections
      (deRhamAlgebras T.toBase).exteriorGenerator.val
      (fun Y x => (deRhamAlgebras T.toBase).squareZero_exteriorGenerator Y x) q (op W)

/-- The exterior power of `formsCompOneRelₛₗ`. -/
abbrev formsPowMap (q : ℕ) (W : T.Y.Opens) :=
  ExteriorAlgebra.powMapₛₗ q (T.sectionRingIso W).toRingHom (T.formsCompOneRelₛₗ W)

/-- **The comparison `Ω^q_{X/S}(A|_W) ⟶ Ω^q_{Y/S}(W)`** on sections: the `q`-th exterior power of
`formsCompOneRel`, followed by the ordered product of the degree-one generators of
`Ω^•_{Y/S}`. -/
def formsCompRel (q : ℕ) (W : T.Y.Opens) :
    (crysDifferentialForms S q).obj (op (T.crystallineThickening.restrictOpen W)) →+
      (relativeDifferentialForms T.toBase (q : ℤ)).val.obj (op W) :=
  (T.formsExtCmp q W).toAddMonoidHom.comp ((T.formsPowMap q W).toAddMonoidHom.comp
      (crysFormSections S q (T.crystallineThickening.restrictOpen W)).toLinearMap.toAddMonoidHom)

/-- `formsCompRel` is the wedge comparison of the exterior power of `formsCompOneRelₛₗ`. -/
theorem formsCompRel_apply (q : ℕ) (W : T.Y.Opens)
    (ω : (crysDifferentialForms S q).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.formsCompRel q W ω = T.formsExtCmp q W (T.formsPowMap q W
      (crysFormSections S q (T.crystallineThickening.restrictOpen W) ω)) := rfl

/-- The restriction map of the crystalline structure ring along `A|_{W'} ⟶ A|_W`. -/
abbrev crysRingRestrict {W W' : T.Y.Opens} (j : W' ⟶ W) :
    crysFormRing S (T.crystallineThickening.restrictOpen W) →+*
      crysFormRing S (T.crystallineThickening.restrictOpen W') :=
  ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map
    ((CrystallineThickening.restrictOpenFunctor T.crystallineThickening).map j).op).hom

/-- `sectionRingIso` is natural in the open. -/
theorem sectionRingIso_naturality {W W' : T.Y.Opens} (j : W' ⟶ W)
    (r : crysFormRing S (T.crystallineThickening.restrictOpen W)) :
    T.sectionRingIso W' (T.crysRingRestrict j r) =
      (T.Y.ringCatSheaf.obj.map j.op).hom (T.sectionRingIso W r) := by
  have hnat := congrArg (fun φ ↦ φ.hom (T.sectionRingIso W r))
    ((Thickening.restrictOpenRingHom T.crystallineThickening.obj).naturality j.op)
  have h1 : ((Thickening.restrictOpenRingHom T.crystallineThickening.obj).app (op W)).hom
      (T.sectionRingIso W r) = r :=
    restrictOpenRingHom_sectionRingEquiv T.crystallineThickening W r
  have h2 : T.crysRingRestrict j r =
      ((Thickening.restrictOpenRingHom T.crystallineThickening.obj).app (op W')).hom
        ((T.Y.ringCatSheaf.obj.map j.op).hom (T.sectionRingIso W r)) := by
    refine Eq.trans ?_ hnat.symm
    exact congrArg (T.crysRingRestrict j) h1.symm
  rw [h2]
  exact (openTopResEquiv T.crystallineThickening W').symm_apply_apply _

/-- `formsCompOneRel` is natural in the open. -/
theorem formsCompOneRel_naturality {W W' : T.Y.Opens} (j : W' ⟶ W)
    (x : (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.formsCompOneRel W' ((crysDifferentials S).map
        ((CrystallineThickening.restrictOpenFunctor T.crystallineThickening).map j).op x) =
      (relativeDifferentials T.toBase).val.map j.op (T.formsCompOneRel W x) :=
  (congrArg (T.relativeDifferentialsIsoDp.inv.val.app (op W')).hom
    (PresheafOfModules.naturality_apply (restrictedToSheaf T.crystallineThickening.obj) j.op
        x)).trans
    (PresheafOfModules.naturality_apply T.relativeDifferentialsIsoDp.inv.val j.op _)

/-- `formsCompRel` is semilinear over `sectionRingIso`. -/
theorem formsCompRel_smul (q : ℕ) (W : T.Y.Opens)
    (r : crysFormRing S (T.crystallineThickening.restrictOpen W))
    (ω : (crysDifferentialForms S q).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.formsCompRel q W (r • ω) = T.sectionRingIso W r • T.formsCompRel q W ω := by
  refine (congrArg (fun z ↦ T.formsExtCmp q W (T.formsPowMap q W z))
    ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).map_smul r ω)).trans ?_
  refine (congrArg (T.formsExtCmp q W) ((T.formsPowMap q W).map_smulₛₗ r _)).trans ?_
  exact (T.formsExtCmp q W).map_smul _ _

/-- `formsCompRel` commutes with restriction to a smaller open. -/
theorem formsCompRel_naturality (q : ℕ) {W W' : T.Y.Opens} (j : W' ⟶ W)
    (ω : (crysDifferentialForms S q).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.formsCompRel q W' ((crysDifferentialForms S q).map
        ((CrystallineThickening.restrictOpenFunctor T.crystallineThickening).map j).op ω) =
      (relativeDifferentialForms T.toBase (q : ℤ)).val.map j.op (T.formsCompRel q W ω) := by
  let k := (CrystallineThickening.restrictOpenFunctor T.crystallineThickening).map j
  let z := crysFormSections S q (T.crystallineThickening.restrictOpen W) ω
  let resc : (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)) →ₛₗ[
      T.crysRingRestrict j] (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen
          W')) :=
    (crysDifferentials S).restrictₛₗ k.op
  have e1 : crysFormSections S q (T.crystallineThickening.restrictOpen W')
      ((crysDifferentialForms S q).map k.op ω) =
        ExteriorAlgebra.powMapₛₗ q (T.crysRingRestrict j) resc z :=
    Subtype.ext rfl
  let χ : crysFormRing S (T.crystallineThickening.restrictOpen W) →+*
      ↑(T.Y.ringCatSheaf.obj.obj (op W')) :=
    (T.sectionRingIso W').toRingHom.comp (T.crysRingRestrict j)
  let v : (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)) →ₛₗ[χ]
      (relativeDifferentials T.toBase).val.obj (op W') :=
    { toFun := fun m ↦ T.formsCompOneRel W' ((crysDifferentials S).map k.op m)
      map_add' := fun m m' ↦ (congrArg (T.formsCompOneRel W')
        (resc.map_add m m')).trans (map_add _ _ _)
      map_smul' := fun r m ↦ (congrArg (T.formsCompOneRel W')
        (resc.map_smulₛₗ r m)).trans
          (T.formsCompOneRel_smul W' _ _) }
  refine (congrArg (fun y ↦ T.formsExtCmp q W' (T.formsPowMap q W' y)) e1).trans ?_
  refine (congrArg (T.formsExtCmp q W') (ExteriorAlgebra.powMapₛₗ_eq_comp q
    resc (T.formsCompOneRelₛₗ W') v (fun _ ↦ rfl)
    (fun _ ↦ rfl) z).symm).trans ?_
  refine (congrArg (T.formsExtCmp q W') (ExteriorAlgebra.powMapₛₗ_eq_comp q
    (T.formsCompOneRelₛₗ W) ((relativeDifferentials T.toBase).val.restrictₛₗ j.op) v
    (fun r ↦ T.sectionRingIso_naturality j r) (fun m ↦ T.formsCompOneRel_naturality j m) z)).trans
        ?_
  exact ((deRhamAlgebras T.toBase).exterior.toPresheafGradedAlgebra.extCmpSections_naturality
    (deRhamAlgebras T.toBase).exteriorGenerator.val
    (fun Y x => (deRhamAlgebras T.toBase).squareZero_exteriorGenerator Y x) q j.op
    (T.formsPowMap q W z)).symm

/-- Over an affine open lying over an affine open of the base, `formsCompOneRel` is bijective:
[Stacks, Tag 07IZ] on sections followed by `Ω_{Y/S,δ} ≅ Ω_{Y/S}`. -/
theorem bijective_formsCompOneRel {W : T.Y.Opens}
    (hW : IsAffineOverAffineOpen T.crystallineThickening.obj W) :
    Function.Bijective (T.formsCompOneRel W) := by
  obtain ⟨hW, V, hV, h⟩ := hW
  have hinv : Function.Bijective (T.relativeDifferentialsIsoDp.inv.val.app (op W)) :=
    ⟨Function.LeftInverse.injective (g := T.relativeDifferentialsIsoDp.hom.val.app (op W))
        (fun x ↦ Stacks.SheafOfModules.hom_val_app_inv_val_app T.relativeDifferentialsIsoDp _ x),
      Function.RightInverse.surjective (g := T.relativeDifferentialsIsoDp.hom.val.app (op W))
        (fun x ↦ Stacks.SheafOfModules.inv_val_app_hom_val_app T.relativeDifferentialsIsoDp _ x)⟩
  exact hinv.comp
    (bijective_restrictedToSheaf_app S T.crystallineThickening.obj hW h hV)

/-- Over an affine open the wedge comparison is the inverse of
`Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso`: both send a wedge to the ordered
product of the generators. -/
theorem formsExtCmp_eq_affineOpenExteriorPowerΓIso_inv (q : ℕ) {W : T.Y.Opens}
    (hW : IsAffineOpen W)
    (z : ⋀[↑(T.Y.ringCatSheaf.obj.obj (op W))]^q ((relativeDifferentials T.toBase).val.obj (op W)))
        :
    T.formsExtCmp q W z = (Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso
      (relativeDifferentials T.toBase) hW
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials T.toBase)) q).inv.hom
        z := by
  have key := ExteriorAlgebra.powExtₛₗ (φ := RingHom.id _) (f := T.formsExtCmp q W)
    (g := (Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso
      (relativeDifferentials T.toBase) hW
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials T.toBase))
          q).inv.hom)
    (fun s ↦ ((deRhamAlgebras T.toBase).exterior.toPresheafGradedAlgebra.extCmpSections_ιMulti
      (deRhamAlgebras T.toBase).exteriorGenerator.val
      (fun Y x => (deRhamAlgebras T.toBase).squareZero_exteriorGenerator Y x) q (op W) s).trans
      (Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_inv_ιMulti
        (relativeDifferentials T.toBase) hW
        (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials T.toBase))
        q s).symm)
  exact LinearMap.congr_fun key z

/-- Over an affine open lying over an affine open of the base, `formsCompRel` is bijective. -/
theorem bijective_formsCompRel (q : ℕ) {W : T.Y.Opens}
    (hW : IsAffineOverAffineOpen T.crystallineThickening.obj W) :
    Function.Bijective (T.formsCompRel q W) := by
  have h3 : Function.Bijective (T.formsExtCmp q W) := by
    have : ⇑(T.formsExtCmp q W) = _ := funext (T.formsExtCmp_eq_affineOpenExteriorPowerΓIso_inv q
        hW.1)
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  exact h3.comp ((ExteriorAlgebra.bijective_powMapₛₗ (T.sectionRingIso W) (T.formsCompOneRelₛₗ W)
    (T.bijective_formsCompOneRel hW) q).comp
      (crysFormSections S q (T.crystallineThickening.restrictOpen W)).bijective)

/-- **The comparison of [Stacks, Tag 07IZ] with the relative differential forms of `Y/S`**, in
degree `q`. -/
def formsComparison (q : ℕ) :
    FormsComparison T.crystallineThickening q (relativeDifferentialForms T.toBase (q : ℤ)) where
  toFun := T.formsCompRel q
  map_smul := T.formsCompRel_smul q
  naturality := fun j ω ↦ T.formsCompRel_naturality q j ω
  bijective := fun _ hW ↦ T.bijective_formsCompRel q hW

/-- The comparison of `formsComparison` on sections is `formsCompRel`. -/
theorem formsComparison_toFun (q : ℕ) (W : T.Y.Opens) :
    (T.formsComparison q).toFun W = T.formsCompRel q W := rfl

/-- `formsCompOneRel` carries the crystalline differential to the universal relative
derivation. -/
theorem formsCompOneRel_crysD (W : T.Y.Opens)
    (b : crysFormRing S (T.crystallineThickening.restrictOpen W)) :
    T.formsCompOneRel W (crysD S (T.crystallineThickening.restrictOpen W) b) =
      (universalRelativeDerivation T.toBase).d (X := op W) (T.sectionRingIso W b) := by
  have e : b = (_root_.Crystalline.openTopRes W).hom (T.sectionRingIso W b) :=
    ((openTopResEquiv T.crystallineThickening W).apply_symm_apply b).symm
  have h1 : (restrictedToSheaf T.crystallineThickening.obj).app (op W)
      (crysD S (T.crystallineThickening.restrictOpen W) b) =
      sheafApp T.crystallineThickening.obj.thickening.target S.S.scheme
        T.crystallineThickening.obj.toBase.hom W (T.sectionRingIso W b) := by
    conv_lhs => rw [e]
    exact restrictedToSheaf_app_d T.crystallineThickening.obj W (T.sectionRingIso W b)
  refine (congrArg (T.relativeDifferentialsIsoDp.inv.val.app (op W)).hom h1).trans ?_
  refine (congrArg (T.relativeDifferentialsIsoDp.inv.val.app (op W)).hom
    (toDpDifferentials_d T.crystallineThickening.obj.thickening.target S.S.scheme
      T.crystallineThickening.obj.toBase.hom W (T.sectionRingIso W b)).symm).trans ?_
  exact Stacks.SheafOfModules.inv_val_app_hom_val_app T.relativeDifferentialsIsoDp _ _

/-- **The comparison on a wedge of crystalline differentials** is the ordered product of the
corresponding relative differentials. -/
theorem formsCompRel_ιMulti (q : ℕ) (W : T.Y.Opens)
    (α : Fin q → (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm
        (exteriorPower.ιMulti _ q α)) =
      (deRhamAlgebras T.toBase).exterior.toPresheafGradedAlgebra.homogeneousProd (op W) q
        fun i ↦ (deRhamAlgebras T.toBase).exteriorGenerator.val.app (op W)
          (T.formsCompOneRel W (α i)) := by
  rw [formsCompRel_apply, LinearEquiv.apply_symm_apply]
  refine (congrArg (T.formsExtCmp q W) (ExteriorAlgebra.powMapₛₗ_ιMulti q _ _ α)).trans ?_
  exact (deRhamAlgebras T.toBase).exterior.toPresheafGradedAlgebra.extCmpSections_ιMulti
      (deRhamAlgebras T.toBase).exteriorGenerator.val
      (fun Y x => (deRhamAlgebras T.toBase).squareZero_exteriorGenerator Y x) q (op W) _

/-- `formsCompRel` on a wedge `α ∧ β₁ ∧ ⋯ ∧ β_q` is the relative exterior product. -/
theorem formsCompRel_leftWedge_ιMulti (q : ℕ) (W : T.Y.Opens)
    (α : (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)))
    (β : Fin q → (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :
    T.formsCompRel (q + 1) W ((crysFormSections S (q + 1) (T.crystallineThickening.restrictOpen
        W)).symm
        (Crystalline.leftWedge q α (exteriorPower.ιMulti _ q β))) =
      relativeExteriorProduct T.toBase q (op W) (T.formsCompOneRel W α)
        (T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm
          (exteriorPower.ιMulti _ q β))) := by
  rw [Crystalline.leftWedge_ιMulti, formsCompRel_ιMulti, formsCompRel_ιMulti]
  refine eq_of_heq ((heq_of_eq (Stacks.GradedAlgebra.homogeneousProd_succ _ (op W) q
    (by push_cast; ring) _)).trans ((Stacks.heq_degCast _ _).trans ?_))
  exact (transportDifferentialForm_heq T.toBase _ (op W) _).symm

/-- **`formsCompRel` carries the crystalline wedge `α ∧ ω` to the relative exterior product.** -/
theorem formsCompRel_leftWedge (q : ℕ) (W : T.Y.Opens)
    (α : (crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)))
    (ω : ⋀[crysFormRing S (T.crystallineThickening.restrictOpen W)]^q
      ((crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)))) :
    T.formsCompRel (q + 1) W ((crysFormSections S (q + 1) (T.crystallineThickening.restrictOpen
        W)).symm
        (Crystalline.leftWedge q α ω)) =
      relativeExteriorProduct T.toBase q (op W) (T.formsCompOneRel W α)
        (T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm
          ω)) := by
  have hmem : ω ∈ Submodule.span (crysFormRing S (T.crystallineThickening.restrictOpen W))
      (Set.range (exteriorPower.ιMulti (crysFormRing S (T.crystallineThickening.restrictOpen W))
          q)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, rfl⟩ := hx
    exact T.formsCompRel_leftWedge_ιMulti q W α β
  | zero =>
    rw [map_zero, map_zero, map_zero, map_zero, map_zero]
    exact (relativeExteriorProduct_zero_right T.toBase q (op W) _).symm
  | add x y _ _ hx hy =>
    rw [map_add, map_add, map_add, hx, hy, map_add, map_add]
    exact (relativeExteriorProduct_add_right T.toBase q (op W) _ _ _).symm
  | smul c x _ hx =>
    rw [map_smul, map_smul, T.formsCompRel_smul, hx, map_smul, T.formsCompRel_smul]
    exact (relativeExteriorProduct_smul_right T.toBase q (op W) _ _ _).symm

/-- `formsCompRel` on a wedge of crystalline differentials of functions. -/
theorem formsCompRel_ιMulti_crysD (q : ℕ) (W : T.Y.Opens)
    (b : Fin q → crysFormRing S (T.crystallineThickening.restrictOpen W)) :
    T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm
        (exteriorPower.ιMulti _ q fun j ↦ crysD S (T.crystallineThickening.restrictOpen W) (b j))) =
      (deRhamAlgebras T.toBase).exterior.toPresheafGradedAlgebra.homogeneousProd (op W) q
          fun i ↦ (deRhamAlgebras T.toBase).exteriorGenerator.val.app (op W)
            ((universalRelativeDerivation T.toBase).d (X := op W) (T.sectionRingIso W (b i))) := by
  rw [formsCompRel_ιMulti]
  congr 1
  funext i
  rw [formsCompOneRel_crysD]

/-- `formsCompRel` on a standard generator `b₀ d b₁ ∧ ⋯ ∧ d b_q`. -/
theorem formsCompRel_crysGen (q : ℕ) (W : T.Y.Opens)
    (b : Fin (q + 1) → crysFormRing S (T.crystallineThickening.restrictOpen W)) :
    T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm
        (b 0 • exteriorPower.ιMulti _ q
          fun j ↦ crysD S (T.crystallineThickening.restrictOpen W) (b j.succ))) =
      T.sectionRingIso W (b 0) • (show (relativeDifferentialForms T.toBase (q : ℤ)).val.obj (op W)
          from
        (deRhamAlgebras T.toBase).exterior.toPresheafGradedAlgebra.homogeneousProd (op W) q
          fun i ↦ (deRhamAlgebras T.toBase).exteriorGenerator.val.app (op W)
            ((universalRelativeDerivation T.toBase).d (X := op W) (T.sectionRingIso W (b i.succ))))
                := by
  rw [map_smul, T.formsCompRel_smul, formsCompRel_ιMulti_crysD]

/-- **The comparison of forms intertwines the de Rham differentials**, on a standard
generator. -/
theorem formsCompRel_deRham_crysGen (q : ℕ) (W : T.Y.Opens)
    (b : Fin (q + 1) → crysFormRing S (T.crystallineThickening.restrictOpen W)) :
    T.formsCompRel (q + 1) W ((crysFormSections S (q + 1) (T.crystallineThickening.restrictOpen
        W)).symm
        (crysDeRhamDifferential S q (T.crystallineThickening.restrictOpen W)
          (b 0 • exteriorPower.ιMulti _ q
            fun j ↦ crysD S (T.crystallineThickening.restrictOpen W) (b j.succ)))) =
      relativeDeRhamDifferentialSection T.toBase q (op W)
        (T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm
          (b 0 • exteriorPower.ιMulti _ q
            fun j ↦ crysD S (T.crystallineThickening.restrictOpen W) (b j.succ)))) := by
  rw [crysDeRhamDifferential_generator, formsCompRel_ιMulti_crysD, formsCompRel_crysGen]
  have hd : relativeDeRhamDifferentialSection T.toBase q (op W) =
      fun ω ↦ ((AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (deRhamAlgebras T.toBase)).differential q).val.app (op W) ω := by
    funext ω
    exact congrArg (fun φ ↦ φ.val.app (op W) ω) (deRhamComplex_d T.toBase q)
  rw [hd]
  have hwedge := AlgebraicGeometry.SheafOfModules.isExactWedge_homogeneousProdLeft
    (deRhamAlgebras T.toBase) (op W) q (fun i ↦ T.sectionRingIso W (b i.succ))
  rw [Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd] at hwedge
  refine eq_of_heq (HEq.trans ?_ ((AlgebraicGeometry.SheafOfModules.deRhamDifferential
    (deRhamAlgebras T.toBase)).generator q (op W) (T.sectionRingIso W (b 0)) _ hwedge).symm)
  refine (heq_of_eq (Stacks.GradedAlgebra.homogeneousProd_succ _ (op W) q
    (by push_cast; ring) _)).trans ((Stacks.heq_degCast _ _).trans ?_)
  exact HEq.rfl

/-- **The comparison of forms intertwines the crystalline de Rham differential of
[Stacks, Tag 07J4] with the relative de Rham differential of `Y/S`.** -/
theorem formsCompRel_deRham (q : ℕ) (W : T.Y.Opens)
    (ω : ⋀[crysFormRing S (T.crystallineThickening.restrictOpen W)]^q
      ((crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W)))) :
    T.formsCompRel (q + 1) W ((crysFormSections S (q + 1) (T.crystallineThickening.restrictOpen
        W)).symm
        (crysDeRhamDifferential S q (T.crystallineThickening.restrictOpen W) ω)) =
      relativeDeRhamDifferentialSection T.toBase q (op W)
        (T.formsCompRel q W ((crysFormSections S q (T.crystallineThickening.restrictOpen W)).symm
          ω)) := by
  have : IsScalarTower ℤ (crysFormRing S (T.crystallineThickening.restrictOpen W))
      ((crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) :=
    IsScalarTower.of_algebraMap_smul fun r m ↦ by
      rw [algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul]
  have hmem : ω ∈ Submodule.span ℤ (Set.range fun c : Fin (q + 1) →
      crysFormRing S (T.crystallineThickening.restrictOpen W) ↦
        c 0 • exteriorPower.ιMulti _ q
          fun i ↦ crysD S (T.crystallineThickening.restrictOpen W) (c i.succ)) := by
    rw [@Crystalline.span_range_smul_ιMulti_eq_top ℤ
      (crysFormRing S (T.crystallineThickening.restrictOpen W))
      ((crysDifferentials S).obj (op (T.crystallineThickening.restrictOpen W))) _ _ _ _ _ _ this
      (crysD S (T.crystallineThickening.restrictOpen W))
      (crysD_span S (T.crystallineThickening.restrictOpen W).obj) q]
    trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact T.formsCompRel_deRham_crysGen q W b
  | zero => simp only [map_zero, relativeDeRhamDifferentialSection_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy, relativeDeRhamDifferentialSection_add]
  | smul c x _ hx => simp only [map_zsmul, hx, relativeDeRhamDifferentialSection_zsmul]

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW
