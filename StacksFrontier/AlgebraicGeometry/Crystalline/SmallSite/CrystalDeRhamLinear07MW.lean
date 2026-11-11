module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseLinearSheaves
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionCrisDeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison

/-!
# The de Rham complex of a crystal as a complex of sheaves of `A`-modules

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], write
`A = Γ(S, 𝒪_S)`, and let `F` be a crystal in quasi-coherent `𝒪_{X/S}`-modules.  The de Rham
complex `K = F ⊗_{𝒪_{X/S}} Ω^•_{X/S}` of [Stacks, Proposition 60.23.1, Tag 07LM] is
`(crystalDeRhamSheafData hF).complex`, a complex of *abelian* sheaves on `Cris(X/S)`.  Part (3) of
[Stacks, Tag 07MW] compares cohomologies in `D(A)`, so `K` has to be read as a complex of sheaves
of `A`-modules (`...SmallSite.BaseModuleSheaf`); this file does that.

The key fact is that the differential is `A`-linear: over an affine-over-affine object it is the
extension `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of the canonical connection, and this extension is linear
over the base (`Crystalline.ExtendedConnection.toLinearMap`), the de Rham differential of
`Ω^*_{X/S}` killing the image of `A`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `presheafBaseAction M` — `A` acting on (the universe lift of) the abelian presheaf underlying a
  presheaf of `𝒪_{X/S}`-modules, through the structure morphisms `T ⟶ S`.
* `linearTensorFormsSheaf F i` — `F ⊗ Ω^i_{X/S}` as a sheaf of `A`-modules.
* `crystalDeRhamLinearDifferential hF i` — the differential, as a morphism of sheaves of
  `A`-modules.
* `crystalDeRhamLinearNatComplex hF`, `crystalDeRhamLinearComplex hF` — **`K` as a complex of
  sheaves of `A`-modules**, `ℕ`- and `ℤ`-indexed.
* `linearCrystalSheaf F` — `F` as a sheaf of `A`-modules, `toBaseModuleSheaf (moduleULift F)`.
* `linearCrystalSingleComplex F` — `F[0]` as a complex of sheaves of `A`-modules.
* `crystalDeRhamLinearTruncation hF` — the truncation map `K ⟶ F[0]`, `A`-linearly.

## Main results

* `crystalDeRhamDifferential_baseAction` — **the differential is `A`-linear**.
* `crystalDeRhamLinearComplexForgetIso` — **the forgetful image of the `A`-linear complex is the
  abelian complex `K`**: `(baseForget S).mapHomologicalComplex _` of
  `crystalDeRhamLinearComplex hF` is isomorphic to `(crystalDeRhamSheafData hF).complex`, the
  isomorphism being the identity in every degree `≥ 0`.
* `linearCrystalSingleComplexForgetIso` — the same for `F[0]` and `singleComplex`.
* `crystalDeRhamLinearNatTruncation_forget` — **the forgetful image of the `A`-linear truncation
  is the truncation of [Stacks, Tag 07LM]**, `CrystalDeRhamSheafData.natTruncation`, through the
  isomorphisms above, and `crystalDeRhamLinearTruncation_forget` the same for the `ℤ`-indexed
  truncation `CrystalDeRhamSheafData.truncation`.
* `linearTensorFormsSheafZeroIso` — **in degree zero the term is `F` as a sheaf of `A`-modules**;
  its forgetful image is `tensorDifferentialFormsSheafZeroIso`.

## What is not proved here

The `A`-linear global sections `...SmallSite.baseLinearGlobalSections` and their derived functor
`...SmallSite.derivedBaseLinearGlobalSectionsFunctor` are in `SmallSite/BaseLinearSheaves.lean`,
with the identification `...SmallSite.toBaseModuleSheafGlobalSectionsIso` of `Γ_A` on
`toBaseModuleSheaf` with the module-valued global sections.  The comparison of
`RΓ_A(Cris(X/S), crystalDeRhamLinearComplex hF)` with
`...SmallSite.moduleULiftDerivedGlobalSections S F` — which needs the acyclicity, for `Γ_A`, of
injective sheaves of `𝒪_{X/S}`-modules and of injective sheaves of `A`-modules — is not proved
here; it is `...SmallSite.moduleULiftDerivedGlobalSectionsIsoLinear` of
`SmallSite/CrystalDeRhamLinearDerived07MW.lean`.

## References

* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The action of `A` on presheaves of `𝒪_{X/S}`-modules -/

/-- The pullback of `a ∈ A = Γ(S, 𝒪_S)` to the ambient scheme of an object of `Cris(X/S)`, as an
element of the ring of sections over which the presheaves of modules of the chapter are
modules. -/
abbrev baseSection (a : Γ(S.S.scheme, ⊤)) (X : (CrystallineThickening S)ᵒᵖ) :
    (structurePresheaf S ⋙ forget₂ CommRingCat RingCat).obj X :=
  (baseRingHom S a).val X

/-- The pullbacks of `a ∈ A` are compatible with the restriction maps of `𝒪_{X/S}`. -/
theorem map_baseSection (a : Γ(S.S.scheme, ⊤)) {X Y : (CrystallineThickening S)ᵒᵖ} (f : X ⟶ Y) :
    (structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map f (baseSection a X) =
      baseSection a Y :=
  (baseRingHom S a).property f

/-- **The global sections of `𝒪_{X/S}` acting on the abelian presheaf underlying a presheaf of
`𝒪_{X/S}`-modules**, lifted to the coefficient universe `u + 1`: a compatible family `r` acts on
the sections over `X` as `r_X`. -/
def globalSectionPresheafAction
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :
    crystallineSectionRing S →+* End ((PresheafOfModules.toPresheaf _).obj M ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}) where
  toFun r := .of
    { app X := AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        ((M.obj X).smul (show (structurePresheaf S ⋙ forget₂ CommRingCat RingCat).obj X from
          r.val X)).asHom
      naturality X Y f := AddCommGrpCat.ext fun x => ULift.ext
        ((congrArg (fun c : (structurePresheaf S ⋙ forget₂ CommRingCat RingCat).obj Y ↦
            c • (show M.obj Y from M.map f (show M.obj X from x.down))) (r.property f)).symm.trans
          (M.map_smul f _ (show M.obj X from x.down)).symm) }
  map_one' := End.ext <| NatTrans.ext <| funext fun X =>
    (congrArg (fun e ↦ AddCommGrpCat.uliftFunctor.{u + 1, u}.map e.asHom)
      (M.obj X).smul.map_one).trans (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_id _)
  map_mul' _ _ := End.ext <| NatTrans.ext <| funext fun X =>
    (congrArg (fun e ↦ AddCommGrpCat.uliftFunctor.{u + 1, u}.map e.asHom)
      ((M.obj X).smul.map_mul _ _)).trans (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_comp _ _)
  map_zero' := End.ext <| NatTrans.ext <| funext fun X =>
    (congrArg (fun e ↦ AddCommGrpCat.uliftFunctor.{u + 1, u}.map e.asHom)
      (M.obj X).smul.map_zero).trans (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_zero _ _)
  map_add' _ _ := End.ext <| NatTrans.ext <| funext fun X =>
    (congrArg (fun e ↦ AddCommGrpCat.uliftFunctor.{u + 1, u}.map e.asHom)
      ((M.obj X).smul.map_add _ _)).trans (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_add)

/-- **`A = Γ(S, 𝒪_S)` acting on the abelian presheaf underlying a presheaf of
`𝒪_{X/S}`-modules**, lifted to the coefficient universe `u + 1`: on the sections over
`(U, T, δ)` an element `a` acts as its pullback to `Γ(T, 𝒪_T)`. -/
def presheafBaseAction
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :
    Γ(S.S.scheme, ⊤) →+* End ((PresheafOfModules.toPresheaf _).obj M ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  (globalSectionPresheafAction M).comp (baseRingHom S)

/-- `presheafBaseAction` on a section. -/
theorem presheafBaseAction_app_apply
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))
    (a : Γ(S.S.scheme, ⊤)) (X : (CrystallineThickening S)ᵒᵖ) (x : ULift.{u + 1} (M.obj X)) :
    (presheafBaseAction M a).asHom.app X x = ULift.up (baseSection a X • x.down) :=
  ULift.ext rfl

/-- **Morphisms of presheaves of `𝒪_{X/S}`-modules are `A`-linear.** -/
theorem presheafBaseAction_naturality
    {M N : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)}
    (g : M ⟶ N) (a : Γ(S.S.scheme, ⊤)) :
    (presheafBaseAction M a).asHom ≫
        Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map g)
          AddCommGrpCat.uliftFunctor.{u + 1, u} =
      Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map g)
          AddCommGrpCat.uliftFunctor.{u + 1, u} ≫ (presheafBaseAction N a).asHom :=
  NatTrans.ext <| funext fun X => AddCommGrpCat.ext fun x => ULift.ext
    ((g.app X).hom.map_smul _ (show M.obj X from x.down))

/-! ### `F ⊗ Ω^i_{X/S}` as a sheaf of `A`-modules -/

variable (F : SheafOfModules.{u} (structureSheaf S))

/-- The sections of the presheaf `F ⊗ Ω^i_{X/S}` over an object, as a module over the ring of
sections of `𝒪_{X/S}` there. -/
abbrev tensorFormsSections (i : ℕ) (X : (CrystallineThickening S)ᵒᵖ) : Type u :=
  ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
    (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj X)

/-- The action of `A` on the abelian sheaf `F ⊗ Ω^i_{X/S}`: the sheafification of
`presheafBaseAction`. -/
def tensorFormsBaseAction (i : ℕ) :
    Γ(S.S.scheme, ⊤) →+* End (tensorDifferentialFormsSheaf F i) :=
  (Stacks.ModuleCatLift.mapEndRingHom (presheafToSheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (tensorFormsULift F i)).comp (presheafBaseAction _)

/-- **`F ⊗ Ω^i_{X/S}` as a sheaf of `A`-modules.** -/
def linearTensorFormsSheaf (i : ℕ) : BaseModuleSheaf S :=
  Stacks.ModuleCatLift.sheafOfEndAction Γ(S.S.scheme, ⊤) (smallTopology S)
    (tensorDifferentialFormsSheaf F i) (tensorFormsBaseAction F i)

/-- The abelian sheaf underlying `linearTensorFormsSheaf F i` is `F ⊗ Ω^i_{X/S}`, on the nose. -/
theorem baseForget_obj_linearTensorFormsSheaf (i : ℕ) :
    (baseForget S).obj (linearTensorFormsSheaf F i) = tensorDifferentialFormsSheaf F i :=
  rfl

/-- The action of `A` on `F ⊗ Ω^i_{X/S}` precomposed with the sheafification unit. -/
theorem toSheafify_tensorFormsBaseAction (i : ℕ) (a : Γ(S.S.scheme, ⊤)) :
    toSheafify (smallTopology S) (tensorFormsULift F i) ≫
        (tensorFormsBaseAction F i a).asHom.hom =
      (presheafBaseAction _ a).asHom ≫ toSheafify (smallTopology S) (tensorFormsULift F i) :=
  (toSheafify_naturality (smallTopology S) (presheafBaseAction _ a).asHom).symm

/-! ### The differential is `A`-linear -/

variable {F} (hF : F.IsQuasicoherentOnSite)
include hF

omit hF in
/-- The pullback of `a ∈ A` to an object of `Cris(X/S)` is its image under the structure map of
the base algebra `Γ(S, 𝒪_S) ⟶ Γ(T, 𝒪_T)`. -/
theorem baseRingHom_val_eq_algebraMap (a : Γ(S.S.scheme, ⊤)) (B : CrystallineThickening S) :
    (show GlobalCrystallineSituation.crysFormRing S B.obj from (baseRingHom S a).val (op B)) =
      algebraMap Γ(S.S.scheme, ⊤) (GlobalCrystallineSituation.crysFormRing S B.obj) a :=
  (congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_eq_app B.obj.toBase.hom)).symm

/-- **The differential over an affine-over-affine object is `A`-linear**: the extension of the
canonical connection is linear over the base. -/
theorem affineDeRhamDifferential_smul (i : ℕ) (B : AffineOverAffineCrystallineThickening S)
    (a : Γ(S.S.scheme, ⊤))
    (x : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i).obj (op B.obj))) :
    affineDeRhamDifferential hF i B (baseSection a (op B.obj) • x) =
      baseSection a (op B.obj) • affineDeRhamDifferential hF i B x := by
  refine (tensorFormsSectionsEquiv F (i + 1) B.obj).injective ?_
  rw [tensorFormsSectionsEquiv_affineDeRhamDifferential]
  have hsmul : ∀ (j : ℕ) (y : ↥((tensorDifferentialForms (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) j).obj (op B.obj))),
      tensorFormsSectionsEquiv F j B.obj (baseSection a (op B.obj) • y) =
        algebraMap Γ(S.S.scheme, ⊤) (GlobalCrystallineSituation.crysFormRing S B.obj.obj) a •
          tensorFormsSectionsEquiv F j B.obj y := fun j y => by
    rw [← baseRingHom_val_eq_algebraMap]
    exact (TensorProduct.congr (LinearEquiv.refl _ (F.val.obj (op B.obj)))
      (crysFormSections S j B.obj)).map_smul _ y
  rw [hsmul, hsmul]
  change (RestrictScalars.addEquiv _ _ _) ((((AffineConnection.ringExtension _ _ _).toLinearMap i))
    ((RestrictScalars.addEquiv _ _ _).symm (algebraMap _ _ a • _))) = _
  rw [RestrictScalars.addEquiv_symm_map_algebraMap_smul, LinearMap.map_smul,
    RestrictScalars.addEquiv_map_smul]
  exact congrArg (_ • ·) (tensorFormsSectionsEquiv_affineDeRhamDifferential hF i B x).symm

/-- **The differential `F ⊗ Ω^i_{X/S} ⟶ F ⊗ Ω^{i+1}_{X/S}` is `A`-linear.**  It commutes with the
action of every `a ∈ A`: the composites agree after the sheafification unit
on every affine-over-affine object, where they are `affineDeRhamDifferential_smul`, and these
objects are cover-dense. -/
theorem crystalDeRhamDifferential_baseAction (i : ℕ) (a : Γ(S.S.scheme, ⊤)) :
    (tensorFormsBaseAction F i a).asHom ≫ crystalDeRhamDifferential hF i =
      crystalDeRhamDifferential hF i ≫ (tensorFormsBaseAction F (i + 1) a).asHom := by
  have key : (presheafBaseAction _ a).asHom ≫ presheafDeRhamDifferential hF i =
      presheafDeRhamDifferential hF i ≫ (tensorFormsBaseAction F (i + 1) a).asHom.hom := by
    refine hom_ext_of_app S (fun B => ?_)
    ext x
    change (presheafDeRhamDifferential hF i).app (op B.obj)
        ((presheafBaseAction _ a).asHom.app (op B.obj) x) =
      (tensorFormsBaseAction F (i + 1) a).asHom.hom.app (op B.obj)
        ((presheafDeRhamDifferential hF i).app (op B.obj) x)
    refine (congrArg ((presheafDeRhamDifferential hF i).app (op B.obj))
      (presheafBaseAction_app_apply _ a _ x)).trans ?_
    refine (presheafDeRhamDifferential_app hF i B _).trans ?_
    refine (congrArg (fun y ↦ (toSheafify (smallTopology S) (tensorFormsULift F (i + 1))).app
      (op B.obj) (ULift.up y)) (affineDeRhamDifferential_smul hF i B a x.down)).trans ?_
    refine (congrArg ((toSheafify (smallTopology S) (tensorFormsULift F (i + 1))).app (op B.obj))
      (presheafBaseAction_app_apply _ a _ (ULift.up (affineDeRhamDifferential hF i B x.down)))
      ).symm.trans ?_
    refine (ConcreteCategory.congr_hom (congrArg (fun α ↦ α.app (op B.obj))
      (toSheafify_tensorFormsBaseAction F (i + 1) a)) _).symm.trans ?_
    exact congrArg ((tensorFormsBaseAction F (i + 1) a).asHom.hom.app (op B.obj))
      (presheafDeRhamDifferential_app hF i B x.down).symm
  refine Sheaf.hom_ext (sheafify_hom_ext (smallTopology S) _ _
    (tensorDifferentialFormsSheaf F (i + 1)).property ?_)
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (crystalDeRhamDifferential hF i).hom)
      (toSheafify_tensorFormsBaseAction F i a)).trans ((Category.assoc _ _ _).trans
        ((congrArg ((presheafBaseAction _ a).asHom ≫ ·)
          (toSheafify_crystalDeRhamDifferential hF i)).trans key)))).trans
    ((congrArg (· ≫ (tensorFormsBaseAction F (i + 1) a).asHom.hom)
      (toSheafify_crystalDeRhamDifferential hF i)).symm.trans (Category.assoc _ _ _))

/-- **The differential of the de Rham complex of `F`, as a morphism of sheaves of `A`-modules.**
Its underlying morphism of abelian sheaves is `crystalDeRhamDifferential hF i`. -/
def crystalDeRhamLinearDifferential (i : ℕ) :
    linearTensorFormsSheaf F i ⟶ linearTensorFormsSheaf F (i + 1) :=
  ObjectProperty.homMk (Stacks.ModuleCatLift.ofEndActionMap Γ(S.S.scheme, ⊤) _ _
    (crystalDeRhamDifferential hF i).hom
    fun a => congrArg (fun φ ↦ φ.hom) (crystalDeRhamDifferential_baseAction hF i a))

/-- The morphism of abelian sheaves underlying `crystalDeRhamLinearDifferential hF i` is
`crystalDeRhamDifferential hF i`. -/
theorem baseForget_map_crystalDeRhamLinearDifferential (i : ℕ) :
    (baseForget S).map (crystalDeRhamLinearDifferential hF i) = crystalDeRhamDifferential hF i :=
  rfl

/-- Consecutive `A`-linear differentials compose to zero. -/
theorem crystalDeRhamLinearDifferential_comp (i : ℕ) :
    crystalDeRhamLinearDifferential hF i ≫ crystalDeRhamLinearDifferential hF (i + 1) = 0 :=
  (baseForget S).map_injective (by
    rw [Functor.map_comp, Functor.map_zero]
    exact crystalDeRhamDifferential_comp hF i)

/-! ### The complex -/

/-- **The de Rham complex `F ⊗ Ω^•_{X/S}` as a complex of sheaves of `A`-modules**, `ℕ`-indexed. -/
def crystalDeRhamLinearNatComplex : CochainComplex (BaseModuleSheaf S) ℕ :=
  CochainComplex.of (fun i ↦ linearTensorFormsSheaf F i) (crystalDeRhamLinearDifferential hF)
    (crystalDeRhamLinearDifferential_comp hF)

/-- **The de Rham complex `F ⊗ Ω^•_{X/S}` as a complex of sheaves of `A`-modules**, extended from
`ℕ` to `ℤ` by zero. -/
abbrev crystalDeRhamLinearComplex : CochainComplex (BaseModuleSheaf S) ℤ :=
  (crystalDeRhamLinearNatComplex hF).extend ComplexShape.embeddingUpNat

/-- The `A`-linear de Rham complex is concentrated in degrees `≥ 0`. -/
instance crystalDeRhamLinearComplex_isStrictlyGE :
    (crystalDeRhamLinearComplex hF).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((crystalDeRhamLinearNatComplex hF).extend ComplexShape.embeddingUpNat) 0)

/-- Forgetting the `A`-action on the `ℕ`-indexed complex gives the abelian complex, degreewise by
the identity. -/
def crystalDeRhamLinearNatComplexForgetIso :
    ((baseForget S).mapHomologicalComplex _).obj (crystalDeRhamLinearNatComplex hF) ≅
      (crystalDeRhamSheafData hF).natComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    rintro i j (rfl : i + 1 = j)
    simp only [Functor.mapHomologicalComplex_obj_d, Iso.refl_hom, crystalDeRhamLinearNatComplex,
      CrystalDeRhamSheafData.natComplex, CochainComplex.of_d]
    rfl)

/-- **The forgetful image of the `A`-linear de Rham complex is the abelian de Rham complex `K`** of
[Stacks, Tag 07LM], `(crystalDeRhamSheafData hF).complex`. -/
def crystalDeRhamLinearComplexForgetIso :
    ((baseForget S).mapHomologicalComplex _).obj (crystalDeRhamLinearComplex hF) ≅
      (crystalDeRhamSheafData hF).complex :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (baseForget S)
      (crystalDeRhamLinearNatComplex hF) ComplexShape.embeddingUpNat).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
      (crystalDeRhamLinearNatComplexForgetIso hF)

/-! ### Degree zero, `F[0]` and the truncation -/

omit hF

variable (F)

/-- **`F` as a sheaf of `A`-modules**: its lift to the module universe `u + 1`, read through
`toBaseModuleSheaf`. -/
abbrev linearCrystalSheaf : BaseModuleSheaf S :=
  (toBaseModuleSheaf S).obj ((moduleULift S).obj F)

/-- The abelian sheaf underlying `linearCrystalSheaf F` is `abelianSheaf F`, on the nose. -/
theorem baseForget_obj_linearCrystalSheaf :
    (baseForget S).obj (linearCrystalSheaf F) = abelianSheaf F :=
  rfl

/-- The presheaf-level identification `F ⊗ Ω^0_{X/S} = F`, on the universe-lifted abelian
presheaves. -/
abbrev tensorFormsZeroPresheafHom :
    tensorFormsULift F 0 ⟶ (abelianSheaf F).obj :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map
    (tensorDifferentialFormsZeroIso (F.val : PresheafOfModules.{u}
      (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))).hom)
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- `tensorDifferentialFormsSheafZeroIso` is the sheafification of the presheaf-level
identification, followed by the inverse of the sheafification unit of the sheaf `abelianSheaf F`. -/
theorem tensorDifferentialFormsSheafZeroIso_hom_hom :
    (tensorDifferentialFormsSheafZeroIso S F).hom.hom =
      sheafifyMap (smallTopology S) (tensorFormsZeroPresheafHom F) ≫
        (isoSheafify (smallTopology S) (abelianSheaf F).property).inv :=
  congrArg (sheafifyMap (smallTopology S) (tensorFormsZeroPresheafHom F) ≫ ·)
    ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).map_preimage _)

/-- The action of `A` on the abelian sheaf `abelianSheaf F` underlying `F` is, on the underlying
presheaf, `presheafBaseAction F.val`. -/
theorem toAbelianSheafBaseAction_moduleULift_hom (a : Γ(S.S.scheme, ⊤)) :
    (toAbelianSheafBaseAction S ((moduleULift S).obj F) a).asHom.hom =
      (presheafBaseAction (F.val : PresheafOfModules.{u}
        (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) a).asHom :=
  NatTrans.ext <| funext fun _ => AddCommGrpCat.ext fun _ => rfl

/-- **The identification `F ⊗ Ω^0_{X/S} = F` is `A`-linear.** -/
theorem tensorDifferentialFormsSheafZeroIso_baseAction (a : Γ(S.S.scheme, ⊤)) :
    (tensorFormsBaseAction F 0 a).asHom ≫ (tensorDifferentialFormsSheafZeroIso S F).hom =
      (tensorDifferentialFormsSheafZeroIso S F).hom ≫
        (toAbelianSheafBaseAction S ((moduleULift S).obj F) a).asHom := by
  refine Sheaf.hom_ext (sheafify_hom_ext (smallTopology S) _ _ (abelianSheaf F).property ?_)
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (tensorDifferentialFormsSheafZeroIso S F).hom.hom)
      (toSheafify_tensorFormsBaseAction F 0 a)).trans ((Category.assoc _ _ _).trans
        ((congrArg ((presheafBaseAction _ a).asHom ≫ ·)
          (toSheafify_tensorDifferentialFormsSheafZeroIso_hom F)).trans
          ((presheafBaseAction_naturality _ a).trans
            (congrArg (tensorFormsZeroPresheafHom F ≫ ·)
              (toAbelianSheafBaseAction_moduleULift_hom F a).symm)))))).trans
    ((congrArg (· ≫ (toAbelianSheafBaseAction S ((moduleULift S).obj F) a).asHom.hom)
      (toSheafify_tensorDifferentialFormsSheafZeroIso_hom F)).symm.trans (Category.assoc _ _ _))

/-- The inverse of the identification `F ⊗ Ω^0_{X/S} = F` is `A`-linear. -/
theorem tensorDifferentialFormsSheafZeroIso_inv_baseAction (a : Γ(S.S.scheme, ⊤)) :
    (toAbelianSheafBaseAction S ((moduleULift S).obj F) a).asHom ≫
        (tensorDifferentialFormsSheafZeroIso S F).inv =
      (tensorDifferentialFormsSheafZeroIso S F).inv ≫ (tensorFormsBaseAction F 0 a).asHom :=
  (Iso.inv_hom_id_assoc (tensorDifferentialFormsSheafZeroIso S F) _).symm.trans
    (congrArg ((tensorDifferentialFormsSheafZeroIso S F).inv ≫ ·)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (tensorDifferentialFormsSheafZeroIso S F).inv)
          (tensorDifferentialFormsSheafZeroIso_baseAction F a).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg ((tensorFormsBaseAction F 0 a).asHom ≫ ·)
              (tensorDifferentialFormsSheafZeroIso S F).hom_inv_id).trans
              (Category.comp_id _))))))

/-- **In degree zero the `A`-linear de Rham complex is `F` as a sheaf of `A`-modules.**  Its
forgetful image is `tensorDifferentialFormsSheafZeroIso`
(`baseForget_map_linearTensorFormsSheafZeroIso`). -/
def linearTensorFormsSheafZeroIso : linearTensorFormsSheaf F 0 ≅ linearCrystalSheaf F where
  hom := ObjectProperty.homMk (Stacks.ModuleCatLift.ofEndActionMap Γ(S.S.scheme, ⊤) _ _
    (tensorDifferentialFormsSheafZeroIso S F).hom.hom
    fun a => congrArg (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).map
      (tensorDifferentialFormsSheafZeroIso_baseAction F a))
  inv := ObjectProperty.homMk (Stacks.ModuleCatLift.ofEndActionMap Γ(S.S.scheme, ⊤) _ _
    (tensorDifferentialFormsSheafZeroIso S F).inv.hom
    fun a => congrArg (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1}).map
      (tensorDifferentialFormsSheafZeroIso_inv_baseAction F a))
  hom_inv_id := (baseForget S).map_injective
    (Iso.hom_inv_id (tensorDifferentialFormsSheafZeroIso S F))
  inv_hom_id := (baseForget S).map_injective
    (Iso.inv_hom_id (tensorDifferentialFormsSheafZeroIso S F))

/-- The forgetful image of `linearTensorFormsSheafZeroIso F` is
`tensorDifferentialFormsSheafZeroIso`. -/
theorem baseForget_map_linearTensorFormsSheafZeroIso :
    (baseForget S).map (linearTensorFormsSheafZeroIso F).hom =
      (tensorDifferentialFormsSheafZeroIso S F).hom :=
  rfl

/-- **`F[0]` as a complex of sheaves of `A`-modules.** -/
abbrev linearCrystalSingleComplex : CochainComplex (BaseModuleSheaf S) ℤ :=
  ((CochainComplex.single₀ (BaseModuleSheaf S)).obj (linearCrystalSheaf F)).extend
    ComplexShape.embeddingUpNat

/-- The complex `F[0]` of sheaves of `A`-modules is concentrated in degrees `≥ 0`. -/
instance linearCrystalSingleComplex_isStrictlyGE :
    (linearCrystalSingleComplex F).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    (((CochainComplex.single₀ (BaseModuleSheaf S)).obj (linearCrystalSheaf F)).extend
      ComplexShape.embeddingUpNat) 0)

/-- The forgetful image of `F[0]` of sheaves of `A`-modules is `F[0]` of abelian sheaves. -/
def linearCrystalSingleComplexForgetIso :
    ((baseForget S).mapHomologicalComplex _).obj (linearCrystalSingleComplex F) ≅
      CrystalDeRhamSheafData.singleComplex (F := F) :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (baseForget S)
      ((CochainComplex.single₀ (BaseModuleSheaf S)).obj (linearCrystalSheaf F))
      ComplexShape.embeddingUpNat).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (baseForget S) (ComplexShape.up ℕ) 0).app
        (linearCrystalSheaf F))

variable {F} (hF : F.IsQuasicoherentOnSite)

/-- The truncation map `K ⟶ F[0]` of sheaves of `A`-modules, `ℕ`-indexed. -/
def crystalDeRhamLinearNatTruncation :
    crystalDeRhamLinearNatComplex hF ⟶
      (CochainComplex.single₀ (BaseModuleSheaf S)).obj (linearCrystalSheaf F) :=
  (CochainComplex.toSingle₀Equiv _ _).symm (linearTensorFormsSheafZeroIso F).hom

/-- **The truncation map `(F → F ⊗ Ω¹ → ⋯) ⟶ F[0]` of [Stacks, Tag 07LM], `A`-linearly.** -/
abbrev crystalDeRhamLinearTruncation :
    crystalDeRhamLinearComplex hF ⟶ linearCrystalSingleComplex F :=
  HomologicalComplex.extendMap (crystalDeRhamLinearNatTruncation hF) ComplexShape.embeddingUpNat

/-- The forgetful image of the `ℕ`-indexed `A`-linear truncation is the `ℕ`-indexed truncation. -/
theorem crystalDeRhamLinearNatTruncation_forget :
    ((baseForget S).mapHomologicalComplex _).map (crystalDeRhamLinearNatTruncation hF) ≫
        ((HomologicalComplex.singleMapHomologicalComplex (baseForget S) (ComplexShape.up ℕ) 0).app
          (linearCrystalSheaf F)).hom =
      (crystalDeRhamLinearNatComplexForgetIso hF).hom ≫
        (crystalDeRhamSheafData hF).natTruncation := by
  refine (CochainComplex.toSingle₀Equiv _ _).injective ?_
  change (baseForget S).map (linearTensorFormsSheafZeroIso F).hom ≫
      ((HomologicalComplex.singleMapHomologicalComplex (baseForget S) (ComplexShape.up ℕ) 0).hom.app
        (linearCrystalSheaf F)).f 0 = 𝟙 _ ≫ (tensorDifferentialFormsSheafZeroIso S F).hom
  refine (congrArg ((baseForget S).map (linearTensorFormsSheafZeroIso F).hom ≫ ·)
    (HomologicalComplex.singleMapHomologicalComplex_hom_app_self (baseForget S)
      (ComplexShape.up ℕ) 0 (linearCrystalSheaf F))).trans ?_
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    Category.id_comp]
  exact baseForget_map_linearTensorFormsSheafZeroIso F

/-- **The forgetful image of the `A`-linear truncation is the truncation of [Stacks, Tag 07LM]**,
`CrystalDeRhamSheafData.truncation`, read through `crystalDeRhamLinearComplexForgetIso` and
`linearCrystalSingleComplexForgetIso`. -/
theorem crystalDeRhamLinearTruncation_forget :
    ((baseForget S).mapHomologicalComplex _).map (crystalDeRhamLinearTruncation hF) ≫
        (linearCrystalSingleComplexForgetIso F).hom =
      (crystalDeRhamLinearComplexForgetIso hF).hom ≫ (crystalDeRhamSheafData hF).truncation := by
  change ((baseForget S).mapHomologicalComplex _).map (HomologicalComplex.extendMap
        (crystalDeRhamLinearNatTruncation hF) ComplexShape.embeddingUpNat) ≫
      ((HomologicalComplex.mapHomologicalComplexExtendIso (baseForget S)
          ((CochainComplex.single₀ (BaseModuleSheaf S)).obj (linearCrystalSheaf F))
          ComplexShape.embeddingUpNat).inv ≫
        HomologicalComplex.extendMap ((HomologicalComplex.singleMapHomologicalComplex (baseForget S)
          (ComplexShape.up ℕ) 0).app (linearCrystalSheaf F)).hom ComplexShape.embeddingUpNat) =
    ((HomologicalComplex.mapHomologicalComplexExtendIso (baseForget S)
          (crystalDeRhamLinearNatComplex hF) ComplexShape.embeddingUpNat).inv ≫
        HomologicalComplex.extendMap (crystalDeRhamLinearNatComplexForgetIso hF).hom
          ComplexShape.embeddingUpNat) ≫
      HomologicalComplex.extendMap (crystalDeRhamSheafData hF).natTruncation
        ComplexShape.embeddingUpNat
  rw [← Category.assoc, HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality,
    Category.assoc, Category.assoc, ← HomologicalComplex.extendMap_comp,
    ← HomologicalComplex.extendMap_comp, crystalDeRhamLinearNatTruncation_forget]
  congr 1


end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
