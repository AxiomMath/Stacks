module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafifyMixed
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderStructureTensorSplitting
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineComparisonAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MK
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionExteriorPower
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorRestrictionAffineChart
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafGlobalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor

/-!
# `(F ⊗ Ω^i_{X/S})_T ≅ F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`

Fix a global crystalline situation `(p, (S, I, γ), X)`, a sheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site `Cris(X/S)` and an object `A = (U, T, δ)` of `Cris(X/S)`.  The terms
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of the de Rham complex of [Stacks, Tag 07LM] restrict to `T`, and
[Stacks, Tag 07IZ] — "`Ω_{X/S}` restricts to `Ω_{T/S,δ}`" — identifies the restrictions with the
terms `F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}` of the de Rham complex of `F_T`.  This file constructs that
identification, as `𝒪_T`-modules and as abelian sheaves on `T_Zar`; it is the termwise input of
the third step of the construction of [Stacks, Equation 07LP].

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `ambientTensorForms` — `F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`, the tensor product of `𝒪_T`-modules of the
  restriction `F_T` with the `i`-th exterior power of the divided power differentials
  `Ω_{T/S,δ}`; `ambientTensorFormsAbelian` is its underlying abelian sheaf at the coefficient
  universe of `Cris(X/S)`.
* `ambientTensorFormsRestriction` — the restriction of `F ⊗ Ω^i_{X/S}` to `T`, as an
  `𝒪_T`-module.
* `ambientTensorFormsRestrictionIso` — **the identification as `𝒪_T`-modules.**
* `restrictTensorDifferentialFormsSheafIso` — **the identification as abelian sheaves**, from the
  restriction to `T` of the abelian sheaf `...SmallSite.tensorDifferentialFormsSheaf F i` to
  `ambientTensorFormsAbelian F A i`; `restrictTensorDifferentialFormsPresheafIso` is the same on
  the underlying presheaves.
* `tensorFormsAmbientComparison` — the map from the restricted presheaf tensor product
  `W ↦ F(A|_W) ⊗ Ω^i_{X/S}(A|_W)` to `F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}` through which sections of the
  former are read in the latter.

## Main results

* `tensorFormsAmbientComparison_eq` — `tensorFormsAmbientComparison` is the Zariski
  sheafification unit of the restricted presheaf tensor product followed by
  `ambientTensorFormsRestrictionIso`.
* `ringRestrictionSheafStructureIso_inv_eq` and
  `crysAmbientSchemeModules_eq_ambientCoefficientModule` — the two identifications of the
  restriction of `𝒪_{X/S}` with `𝒪_T` used in the library agree, so the two spellings of `F_T`
  agree.

## Implementation notes

The identification is a chain of four steps, each already in the library in some form: the
restriction of a crystalline sheafification is a Zariski sheafification
(`...SmallSite.restrictOpenTensorSheafIso`); restriction of scalars along an isomorphism of
sheaves of rings commutes with sheafification
(`PresheafOfModules.sheafificationRestrictScalarsIso`) and with the objectwise tensor product
(`PresheafOfModules.restrictScalarsTensorObjIso`); [Stacks, Tag 0GMW] with one factor a sheaf
(`PresheafOfModules.tensorSheafifyMixedIso`); and [Stacks, Tag 07IZ] in every degree
(`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialFormsSheafExteriorPowerIso`).

## References

* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  MonoidalCategory

universe v u₁ u

noncomputable section

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}}

/-- Restriction of scalars along `β` and then along `γ`, with `γ ≫ β = 𝟙` on sections, is
isomorphic to the identity: the identity map of sections is linear for the two scalar
multiplications. -/
def restrictScalarsRestrictScalarsIso (β : R ⟶ R') (γ : R' ⟶ R)
    (h : ∀ (X : Cᵒᵖ) (r : R'.obj X), β.app X (γ.app X r) = r)
    (N : PresheafOfModules.{u} R') :
    (restrictScalars γ).obj ((restrictScalars β).obj N) ≅ N :=
  PresheafOfModules.isoMk (fun X ↦ LinearEquiv.toModuleIso
    (show ((restrictScalars γ).obj ((restrictScalars β).obj N)).obj X ≃ₗ[R'.obj X] N.obj X from
    { toFun x := x
      map_add' _ _ := rfl
      map_smul' r x := by
        change (β.app X (γ.app X r)) • (show N.obj X from x) = r • (show N.obj X from x)
        rw [h X r]
      invFun x := x
      left_inv _ := rfl
      right_inv _ := rfl })) (fun _ _ _ ↦ rfl)

end PresheafOfModules

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] Crystalline.monoidalCategorySchemeModules

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  (A : CrystallineThickening S) (i : ℕ)

/-- **Restriction of scalars from the restriction of `𝒪_{X/S}` to `𝒪_T` commutes with
sheafification.** -/
def ambientRestrictScalarsSheafificationIso
    (N : PresheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj).obj) :
    (SheafOfModules.restrictScalars (ambientRingSheafIso A).inv).obj
        ((PresheafOfModules.sheafification (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).obj
          N) ≅
      (PresheafOfModules.sheafification (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj)).obj
        ((PresheafOfModules.restrictScalars (ambientRingSheafIso A).inv.hom).obj N) :=
  (SheafOfModules.restrictScalars (ambientRingSheafIso A).inv).mapIso
      ((PresheafOfModules.sheafification
        (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)).mapIso
          (PresheafOfModules.restrictScalarsRestrictScalarsIso (ambientRingSheafIso A).inv.hom
            (ambientRingSheafIso A).hom.hom (fun X r ↦ by
              have h := congrArg (fun f ↦ f.hom.app X) (ambientRingSheafIso A).hom_inv_id
              exact RingHom.congr_fun (congrArg RingCat.Hom.hom h) r) N).symm) ≪≫
    (PresheafOfModules.sheafificationRestrictScalarsIso (ambientRingSheafIso A).symm
      ((PresheafOfModules.restrictScalars (ambientRingSheafIso A).inv.hom).obj N)).symm

/-- The identification of the restriction of `𝒪_{X/S}` to the opens of `T` with `𝒪_T`, as an
isomorphism of presheaves of rings, in the direction `𝒪_T ⟶ 𝒪_{X/S}|_T` of
`...Thickening.restrictOpenRingHom`. -/
abbrev ambientRingPresheafIso :
    A.obj.thickening.target.scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat ≅
      restrictedCommRing A ⋙ forget₂ CommRingCat RingCat :=
  (sheafToPresheaf _ _).mapIso (ambientRingSheafIso A).symm

/-- **The restriction to `T` of the presheaf tensor product `F ⊗ Ω^i_{X/S}`, read over `𝒪_T`, is
the presheaf tensor product over `𝒪_T` of `F_T` with the restriction of `Ω^i_{X/S}`.**  Both are
sectionwise `F(A|_W) ⊗ Ω^i_{X/S}(A|_W)`, over two rings identified by `restrictOpenRingHom`. -/
def tensorRestrictionAmbientIso :
    (PresheafOfModules.restrictScalars (ambientRingPresheafIso A).hom).obj
        (restrictedModule A
          (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))) ⊗
        (PresheafOfModules.restrictScalars (ambientRingPresheafIso A).hom).obj
          (restrictedModule A (crysDifferentialForms S i)) ≅
      (PresheafOfModules.restrictScalars (ambientRingPresheafIso A).hom).obj
        (tensorRestriction A F i) :=
  PresheafOfModules.restrictScalarsTensorObjIso A.obj.thickening.target.scheme.sheaf.obj
    (restrictedCommRing A) (ambientRingPresheafIso A)
    (restrictedModule A
      (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)))
    (restrictedModule A (crysDifferentialForms S i))

/-- **The restriction of `F ⊗ Ω^i_{X/S}` to `T`, as an `𝒪_T`-module**: the associated sheaf over
the restriction of `𝒪_{X/S}` of the restricted presheaf tensor product, with its scalars read in
`𝒪_T` along `...SmallSite.ambientRingSheafIso`.  Its underlying abelian presheaf is that of
`...SmallSite.tensorRestrictionSheaf`. -/
def ambientTensorFormsRestriction : A.obj.thickening.target.scheme.Modules :=
  (SheafOfModules.restrictScalars (ambientRingSheafIso A).inv).obj (tensorRestrictionSheaf A F i)

/-- The first two steps: `ambientTensorFormsRestriction` is the associated sheaf over `𝒪_T` of the
presheaf tensor product of `F_T` with the restriction of `Ω^i_{X/S}`. -/
def ambientTensorFormsRestrictionIsoSheafify :
    ambientTensorFormsRestriction F A i ≅
      (PresheafOfModules.sheafification (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj)).obj
        (PresheafOfModules.tensorObj
          ((PresheafOfModules.restrictScalars (ambientRingPresheafIso A).hom).obj
            (restrictedModule A
              (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))))
          ((PresheafOfModules.restrictScalars (ambientRingPresheafIso A).hom).obj
            (restrictedModule A (crysDifferentialForms S i)))) :=
  ambientRestrictScalarsSheafificationIso A (tensorRestriction A F i) ≪≫
    (PresheafOfModules.sheafification (𝟙 A.obj.thickening.target.scheme.ringCatSheaf.obj)).mapIso
      (tensorRestrictionAmbientIso F A i).symm

/-- **The two identifications of `𝒪_{X/S}|_T` with `𝒪_T` agree.**  Over an open `W` of `T` both are
the restriction map of `𝒪_T` from `W` to the image of `W` under its open immersion, which is `W`
again. -/
theorem ringRestrictionSheafStructureIso_inv_eq :
    (Thickening.ringRestrictionSheafStructureIso A.obj).inv = (ambientRingSheafIso A).inv := by
  apply Sheaf.hom_ext
  ext W : 2
  show (forget₂ CommRingCat RingCat).map (Scheme.Opens.topIso W.unop).inv =
    (forget₂ CommRingCat RingCat).map (openTopRes W.unop)
  rw [openTopRes_eq]
  rfl

/-- **The two spellings of `F_T` agree**: `...SmallSite.crysAmbientSchemeModules` and
`...SmallSite.ambientCoefficientModule` are the restriction of scalars of the same sheaf of
modules along the same isomorphism of sheaves of rings, by
`ringRestrictionSheafStructureIso_inv_eq`. -/
theorem crysAmbientSchemeModules_eq_ambientCoefficientModule :
    crysAmbientSchemeModules F A = ambientCoefficientModule A F := by
  show (SheafOfModules.restrictScalars
      (Thickening.ringRestrictionSheafStructureIso A.obj).inv).obj
        (CohomologyRestriction.moduleRestrictionSheaf F A) =
    (SheafOfModules.restrictScalars (ambientRingSheafIso A).inv).obj
      (CohomologyRestriction.moduleRestrictionSheaf F A)
  rw [ringRestrictionSheafStructureIso_inv_eq]

/-- **`F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`**, the degree-`i` term of the de Rham complex of the restriction
`F_T` of a sheaf of `𝒪_{X/S}`-modules `F` to the ambient scheme `T` of an object `(U, T, δ)` of
`Cris(X/S)`: the tensor product, as `𝒪_T`-modules, of `F_T` with the `i`-th exterior power of the
sheaf `Ω_{T/S,δ}` of divided power differentials of [Stacks, Tag 07IW]. -/
def ambientTensorForms : A.obj.thickening.target.scheme.Modules :=
  crysAmbientSchemeModules F A ⊗
    Scheme.Modules.exteriorPower
      (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom) (i : ℤ)

/-- **[Stacks, Tag 07IZ] for `F ⊗ Ω^i_{X/S}`:
`(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})_T ≅ F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`** as `𝒪_T`-modules, for every sheaf
of `𝒪_{X/S}`-modules `F`, every object `(U, T, δ)` of `Cris(X/S)` and every `i`.

The restriction of the presheaf tensor product is the presheaf tensor product of the
restrictions (`tensorRestrictionAmbientIso`); sheafifying, the first factor `F_T` is already a
sheaf, so the associated sheaf is `F_T ⊗ (Ω^i_{X/S})_T` by [Stacks, Tag 0GMW]
(`PresheafOfModules.tensorSheafifyMixedIso`); and `(Ω^i_{X/S})_T ≅ ⋀^i Ω_{T/S,δ}` is
[Stacks, Tag 07IZ] in every degree,
`Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialFormsSheafExteriorPowerIso`. -/
def ambientTensorFormsRestrictionIso :
    ambientTensorFormsRestriction F A i ≅ ambientTensorForms F A i :=
  ambientTensorFormsRestrictionIsoSheafify F A i ≪≫
    (PresheafOfModules.tensorSheafifyMixedIso.{u, u, u, u, u}
      (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (𝟙 A.obj.thickening.target.scheme.sheaf.obj) (ambientCoefficientModule A F)
      ((PresheafOfModules.restrictScalars (ambientRingPresheafIso A).hom).obj
        (restrictedModule A (crysDifferentialForms S i)))).symm ≪≫
    whiskerLeftIso (ambientCoefficientModule A F)
      (restrictedCrysDifferentialFormsSheafExteriorPowerIso S A.obj i) ≪≫
    eqToIso (by rw [ambientTensorForms, crysAmbientSchemeModules_eq_ambientCoefficientModule])

/-- **`F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}` as an abelian sheaf on `T_Zar`**, read at the coefficient universe
`u + 1` of the cohomology of `Cris(X/S)`. -/
def ambientTensorFormsAbelian :
    Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    ((SheafOfModules.toSheaf _).obj (ambientTensorForms F A i))

/-- The identification of the second step of `restrictTensorDifferentialFormsSheafIso` on the
underlying abelian presheaves: `ambientTensorFormsRestrictionIso`, raised to the universe
`u + 1`. -/
def ambientTensorFormsULiftIso :
    tensorRestrictionSheafULift A F i ≅ (ambientTensorFormsAbelian F A i).obj :=
  Functor.isoWhiskerRight
    ((PresheafOfModules.toPresheaf _).mapIso
      ((SheafOfModules.forget _).mapIso (ambientTensorFormsRestrictionIso F A i)))
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- `restrictTensorDifferentialFormsSheafIso` on the underlying abelian presheaves: the
restriction to `T` of the crystalline sheafification of `F ⊗ Ω^i_{X/S}` is the abelian presheaf of
`F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`. -/
def restrictTensorDifferentialFormsPresheafIso :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙
        sheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i) ≅
      (ambientTensorFormsAbelian F A i).obj :=
  restrictOpenTensorSheafIso A F i ≪≫ ambientTensorFormsULiftIso F A i

/-- **[Stacks, Tag 07IZ] for the terms of the de Rham complex of `F`: the restriction to `T` of the
abelian sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on `Cris(X/S)` is `F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`.**

The restriction of the crystalline sheafification is the Zariski sheafification of the restricted
presheaf tensor product (`...SmallSite.restrictOpenTensorSheafIso`), and that is, as an
`𝒪_T`-module, `F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}` by `ambientTensorFormsRestrictionIso`. -/
def restrictTensorDifferentialFormsSheafIso :
    (CrystallineThickening.abelianAmbientRestriction A).obj (tensorDifferentialFormsSheaf F i) ≅
      ambientTensorFormsAbelian F A i :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (restrictTensorDifferentialFormsPresheafIso F A i)

/-- **The comparison `F(A|_W) ⊗ Ω^i_{X/S}(A|_W) ⟶ (F_T ⊗_{𝒪_T} Ω^i_{T/S,δ})(W)` on sections**
over the opens `W` of `T`, at the universe `u + 1`: the image in `F ⊗ Ω^i_{X/S}` of a section of
the presheaf tensor product, read in `F_T ⊗ Ω^i_{T/S,δ}` through
`restrictTensorDifferentialFormsSheafIso`.  It is the Zariski sheafification unit of the
restricted presheaf tensor product followed by `ambientTensorFormsRestrictionIso`
(`tensorFormsAmbientComparison_eq`). -/
def tensorFormsAmbientComparison :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ tensorDifferentialFormsPresheaf F i ⟶
      (ambientTensorFormsAbelian F A i).obj :=
  Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
      (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) ≫
    (restrictTensorDifferentialFormsPresheafIso F A i).hom

/-- **`tensorFormsAmbientComparison` is the Zariski sheafification unit of the restricted presheaf
tensor product, followed by `ambientTensorFormsRestrictionIso`.** -/
theorem tensorFormsAmbientComparison_eq :
    tensorFormsAmbientComparison F A i =
      tensorRestrictionSheafULiftUnit A F i ≫ (ambientTensorFormsULiftIso F A i).hom := by
  unfold tensorFormsAmbientComparison
  rw [restrictTensorDifferentialFormsPresheafIso, Iso.trans_hom, ← Category.assoc,
    whiskerLeft_toSheafify_comp_restrictOpenTensorSheafIso_hom]

/-- `tensorFormsAmbientComparison` over an open of `T`. -/
theorem tensorFormsAmbientComparison_app (W : A.obj.thickening.target.scheme.Opens) :
    (tensorFormsAmbientComparison F A i).app (op W) =
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))).app (op W) ≫
        (restrictTensorDifferentialFormsPresheafIso F A i).hom.app (op W) :=
  NatTrans.comp_app _ _ _

/-- `tensorFormsAmbientComparison` on sections: the restricted crystalline sheafification unit,
followed by `restrictTensorDifferentialFormsPresheafIso`. -/
theorem tensorFormsAmbientComparison_app_apply (W : A.obj.thickening.target.scheme.Opens)
    (x : ((CrystallineThickening.restrictOpenFunctor A).op ⋙
      tensorDifferentialFormsPresheaf F i).obj (op W)) :
    (tensorFormsAmbientComparison F A i).app (op W) x =
      (restrictTensorDifferentialFormsPresheafIso F A i).hom.app (op W)
        ((Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))).app (op W) x) :=
  (ConcreteCategory.congr_hom (tensorFormsAmbientComparison_app F A i W) x).trans
    (ConcreteCategory.comp_apply _ _ x)

end Crystalline.GlobalCrystallineSituation.SmallSite
